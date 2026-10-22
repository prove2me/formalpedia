-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_fderiv_lift_le
-- name    : JHolomorphic.eLpNorm_fderiv_lift_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T22:39:10.552992+00:00
-- url     : https://prove2.me/theorems/a801795e-8cf4-46d7-8cee-0c63b2c409c9
-- title:
--   An $L^p$ bound for the derivative of the lift $z\mapsto(u(z),Du(z)e)$ on a compact set
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $U\subseteq\mathbb{C}$ open, $u:U\to E$ smooth, $1\le p<\infty$, $e\in\mathbb{C}$ with $|e|\le1$, and $K\subseteq U$ compact. If $\|Du\|_{L^p(K)}\le C_1$ and $\|D^2u\|_{L^p(K)}\le C_2$, then the map $v(w)=\bigl(u(w),Du(w)e\bigr)$ satisfies
--   $$\|Dv\|_{L^p(K)}\le C_1+C_2.$$
--   This bound transfers $W^{2,p}$ bounds on $u$ to $W^{1,p}$ bounds on its tangent lifts.
--
--   **Formalization Note** The hypotheses are `ContDiffOn ℝ ∞ u U`, `IsOpen U`, `K' ⊆ U`, `IsCompact K'` and `1 ≤ p`. The norms are `eLpNorm _ (ENNReal.ofReal p) (volume.restrict K')` of `fderiv ℝ u`, `fderiv ℝ (fderiv ℝ u)` and `fderiv ℝ (fun z => (u z, fderiv ℝ u z e))`, with `C₁ C₂ : ℝ≥0`.
-- source:
--   Elementary differential calculus; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.22

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Normed.Operator.Prod

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

/-- Let `1 ≤ p` and let `u` be `C^∞` on an open set `U ⊆ ℂ`. For `‖e‖ ≤ 1` and a compact
`K ⊆ U`, the `L^p(K)` norm of the derivative of the lift `z ↦ (u(z), Du(z) e)` is at most
`C₁ + C₂` whenever `‖Du‖_{L^p(K)} ≤ C₁` and `‖D²u‖_{L^p(K)} ≤ C₂`. -/
theorem eLpNorm_fderiv_lift_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 ≤ p) (U : Set ℂ) (hU : IsOpen U) (u : ℂ → E)
    (hu : ContDiffOn ℝ ∞ u U) (e : ℂ) (he : ‖e‖ ≤ 1) (K' : Set ℂ) (hK'U : K' ⊆ U)
    (hK' : IsCompact K') (C₁ C₂ : ℝ≥0)
    (h1 : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict K') ≤ C₁)
    (h2 : eLpNorm (fderiv ℝ (fderiv ℝ u)) (ENNReal.ofReal p) (volume.restrict K') ≤ C₂) :
    eLpNorm (fderiv ℝ (fun z => (u z, fderiv ℝ u z e))) (ENNReal.ofReal p)
      (volume.restrict K') ≤ (C₁ + C₂ : ℝ≥0) := by
  sorry

end JHolomorphic
