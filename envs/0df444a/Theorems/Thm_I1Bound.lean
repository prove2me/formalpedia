-- Prove2me | Theorems.Thm_I1Bound
-- name    : I1Bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:46:45.130396+00:00
-- url     : https://prove2.me/theorems/fada3ce7-c6b6-4134-bf21-e803abd6dd75
-- title:
--   Bound $O\!\left(\frac{X \log X}{\varepsilon T}\right)$ for the lower vertical tail $I_1$ in the smoothed Perron contour
-- statement:
--   Let $\nu : \mathbb{R} \to \mathbb{R}$ be a smoothing function with support contained in $[1/2, 2]$, of class $C^1$, nonnegative on $(0,\infty)$, and normalized by the multiplicative mass condition $\int_0^\infty \nu(x)\,\frac{dx}{x} = 1$. In the contour decomposition of the smoothed Chebyshev function $\psi_\varepsilon(X)$, let
--   $$I_1(\nu, \varepsilon, X, T) = \frac{1}{2\pi i}\, i \int_{-\infty}^{-T} F\Bigl(1 + \tfrac{1}{\log X} + it\Bigr)\, dt$$
--   denote the lower infinite tail of the integral along the vertical line $\operatorname{Re} s = 1 + 1/\log X$, where $F$ is the smoothed Chebyshev integrand $F(s) = -\frac{\zeta'}{\zeta}(s)\, \mathcal{M}(\tilde\nu_\varepsilon)(s)\, X^s$ built from the Mellin transform of the $\varepsilon$-rescaled mollifier.
--
--   Then there is a constant $C > 0$, depending only on $\nu$, such that for all $\varepsilon \in (0,1)$, all $X > 3$, and all $T > 3$:
--   $$\|I_1(\nu, \varepsilon, X, T)\| \leq \frac{C\, X \log X}{\varepsilon\, T}.$$
--
--   The rapid decay of the Mellin transform of the smooth mollifier in vertical strips makes the tail integral converge and yields the quantitative saving $1/T$; the factors $X \log X$ and $1/\varepsilon$ come from the line $\operatorname{Re} s = 1 + 1/\log X$ and from the scaling of the mollifier.
--
--   This is one of the estimates for the pieces $I_1, \dots, I_9$ into which the PNT+ project splits the Perron contour for $\psi_\varepsilon(X)$; choosing $T$ and $\varepsilon$ appropriately as functions of $X$, these bounds combine to give the Prime Number Theorem with an explicit error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L1407-L1716

import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_MediumPNT_defs
import Definitions.Def_MellinCalculus_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open Chebyshev

open ComplexConjugate

open MeasureTheory

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by sorry
