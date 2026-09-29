-- Prove2me | Theorems.Thm_I3Bound
-- name    : I3Bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:48:20.768258+00:00
-- url     : https://prove2.me/theorems/7870ba8b-60ef-47e1-b844-71a897fae12a
-- title:
--   Bound $O\!\left(\frac{X \cdot X^{-A/\log^9 T}}{\varepsilon}\right)$ for the shifted vertical segment $I_3$
-- statement:
--   Let $\nu : \mathbb{R} \to \mathbb{R}$ be a $C^1$ smoothing function supported in $[1/2, 2]$. Assume the zero-free-region bound: constants $A \in (0,1/2]$ and $C_\zeta > 0$ satisfy
--   $$\left\|\frac{\zeta'}{\zeta}(\sigma + it)\right\| \leq C_\zeta \log^9|t| \quad \text{for } |t| > 3,\ \sigma \geq 1 - \frac{A}{\log^9 |t|}.$$
--   In the contour decomposition of the smoothed Chebyshev function, let
--   $$I_3(\nu, \varepsilon, T, X, \sigma_1) = \frac{1}{2\pi i}\, i \int_{-T}^{-3} F(\sigma_1 + it)\, dt$$
--   be the portion of the shifted vertical line $\operatorname{Re} s = \sigma_1$ with $t$ ranging from $-T$ to $-3$, where $F$ is the smoothed Chebyshev integrand.
--
--   Then there exists $C > 0$ such that for all $X > 3$, all $\varepsilon \in (0,1)$, and all $T > 3$, with $\sigma_1 = 1 - A/\log^9 T$:
--   $$\|I_3(\nu, \varepsilon, T, X, \sigma_1)\| \leq \frac{C\, X \cdot X^{-A/\log^9 T}}{\varepsilon}.$$
--
--   Along the shifted line the factor $|X^s| = X^{\sigma_1} = X \cdot X^{-A/\log^9 T}$ produces the crucial power saving, while the $\zeta'/\zeta$ bound and the decay of the Mellin transform of the mollifier keep the $t$-integral bounded uniformly in $T$ (at the cost of $1/\varepsilon$).
--
--   This is the main "saving" leg of the rectangular contour: after balancing $T$ against $X$, the factor $X^{-A/\log^9 T}$ becomes $\exp(-c \log X / \log^9 T)$-type decay, which is precisely the source of the error term in the version of the Prime Number Theorem proved in the PNT+ project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L2184-L2453

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
set_option maxHeartbeats 400000

theorem I3Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X)
        {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
        {T : ℝ} (_ : 3 < T),
        let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
        ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by sorry
