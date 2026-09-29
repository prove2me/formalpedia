-- Prove2me | Theorems.Thm_I2Bound
-- name    : I2Bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:47:19.0992+00:00
-- url     : https://prove2.me/theorems/6b48ef5e-8e29-46ab-ac37-ded8c69ab3ef
-- title:
--   Bound $O\!\left(\frac{X}{\varepsilon T}\right)$ for the horizontal segment $I_2$ of the smoothed Perron contour
-- statement:
--   Let $\nu : \mathbb{R} \to \mathbb{R}$ be a $C^1$ smoothing function supported in $[1/2, 2]$. Assume the logarithmic-derivative bound hypothesis: there are constants $A \in (0, 1/2]$ and $C_2 > 0$ such that for all $t$ with $|t| > 3$ and all $\sigma \geq 1 - A/\log^9 |t|$,
--   $$\left\| \frac{\zeta'}{\zeta}(\sigma + it) \right\| \leq C_2 \log^9 |t|.$$
--   In the contour decomposition of the smoothed Chebyshev function, let
--   $$I_2(\nu, \varepsilon, T, X, \sigma_1) = \frac{1}{2\pi i} \int_{\sigma_1}^{1 + 1/\log X} F(\sigma - iT)\, d\sigma$$
--   be the bottom horizontal segment at height $-T$ joining the abscissa $\sigma_1$ to the line $1 + 1/\log X$, where $F$ is the smoothed Chebyshev integrand built from $-\zeta'/\zeta$, the Mellin transform of the rescaled mollifier, and $X^s$.
--
--   Then there exists a constant $C > 0$ such that for all $X > 3$, all $\varepsilon \in (0,1)$, and all $T > 3$, with $\sigma_1 = 1 - A/\log^9 T$:
--   $$\|I_2(\nu, \varepsilon, T, X, \sigma_1)\| \leq \frac{C\, X}{\varepsilon\, T}.$$
--
--   The segment has length $O(1/\log T)$ inside the zero-free region, where $\zeta'/\zeta$ is polynomially bounded in $\log T$, while the Mellin factor supplies decay of order $1/(\varepsilon T^2)$ at height $T$; together these give the stated $X/(\varepsilon T)$ estimate.
--
--   This estimate controls one of the two horizontal crossbars (the other is its mirror image at height $+T$) in the rectangular contour used by the PNT+ project to shift the Perron integral for $\psi_\varepsilon(X)$ into the zero-free region, a step in proving the Prime Number Theorem with error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L1754-L1898

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

theorem I2Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T) := by sorry
