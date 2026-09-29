-- Prove2me | Theorems.Thm_I5Bound
-- name    : I5Bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:49:23.368702+00:00
-- url     : https://prove2.me/theorems/296e0dd2-0444-4216-8c4b-98e618285fd7
-- title:
--   Bound $\|I_5\| \le C\,X^{\sigma_2}/\varepsilon$ for the left vertical contour piece in the smoothed PNT argument
-- statement:
--   Let $\nu\colon\mathbb{R}\to\mathbb{R}$ be a smoothing function of class $C^1$ whose support is contained in $[1/2,2]$. Let $\sigma_2\in(0,1)$ be an abscissa for which the logarithmic derivative $\zeta'/\zeta$ of the Riemann zeta function is holomorphic on the small rectangle $[\sigma_2,2]\times[-3,3]$ punctured at $s=1$ (the hypothesis `LogDerivZetaIsHoloSmall`).
--
--   In the contour-pulling proof of the medium-strength Prime Number Theorem, the smoothed Chebyshev function is expressed as a vertical contour integral of $-\frac{\zeta'}{\zeta}(s)\,\mathcal{M}(\widetilde{1_{\varepsilon}})(s)\,X^s$, and the contour is deformed into finitely many pieces $I_1,\dots,I_9$; here $I_5$ denotes the piece running along the vertical segment at real part $\sigma_2$ near the real axis (imaginary part in $[-3,3]$). The theorem asserts a uniform bound: there exists a constant $C>0$ such that
--
--   $$\|I_5(\nu,\varepsilon,X,\sigma_2)\| \le \frac{C\, X^{\sigma_2}}{\varepsilon}$$
--
--   for every $X>3$ and every $\varepsilon\in(0,1)$, where $\varepsilon$ is the width parameter of the mollified cutoff $\widetilde{1_{\varepsilon}}$ (`Smooth1`).
--
--   Since $\sigma_2<1$, the factor $X^{\sigma_2}$ is a genuine power saving over the main term $X$: after choosing $\varepsilon$ as a suitable function of $X$, this piece is absorbed into the error term $O\bigl(X\exp(-c(\log X)^{1/10})\bigr)$ of the Prime Number Theorem. The lemma is one of the nine contour-piece estimates that together drive the quantitative PNT in this development.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L2887-L3035

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

theorem I5Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    : ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε := by sorry
