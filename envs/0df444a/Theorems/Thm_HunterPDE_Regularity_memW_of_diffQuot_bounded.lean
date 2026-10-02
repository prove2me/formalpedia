-- Prove2me | Theorems.Thm_HunterPDE_Regularity_memW_of_diffQuot_bounded
-- name    : HunterPDE.Regularity.memW_of_diffQuot_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T19:34:04.841439+00:00
-- url     : https://prove2.me/theorems/8408edfc-002b-45d2-8fe7-d2f829af326c
-- title:
--   Theorem 4.53 (2) — uniformly bounded difference quotients imply W^{1,p}(Ω′)
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open, $\Omega' \Subset \Omega$ and $d = \operatorname{dist}(\Omega', \partial\Omega) > 0$. Let $1 < p < \infty$ and $u \in L^p(\Omega)$. If there is a constant $C$ such that $\|D^h u\|_{L^p(\Omega')} \le C$ for all $0 < |h| < d/2$, then $u \in W^{1,p}(\Omega')$ and
--   $$\|Du\|_{L^p(\Omega')} \le C .$$
--
--   This is the converse direction of the difference-quotient characterization: a bound uniform in $h$ produces weak derivatives in $L^p$, which is how second weak derivatives are obtained in the proof of Theorem 4.27.
--
--   **Formalization Note.** $\|D^h u\|_{L^p(\Omega')}$ is the $L^p(\Omega')$ norm of $|D^h u| = (\sum_i (D_i^h u)^2)^{1/2}$ and $\|Du\|_{L^p(\Omega')}$ that of $|Du| = (\sum_i (\partial_i u)^2)^{1/2}$ with the weak derivatives taken on $\Omega'$. $C$ is real and compared through `ENNReal.ofReal C`. The distance $d$ is modelled as in Theorem 4.53 (1). $p$ is `p : ℝ≥0∞` with `1 < p`, `p ≠ ∞`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 125, Theorem 4.53 (2)

import Mathlib
import Definitions.Def_HunterPDE_Regularity_Sobolev
import Definitions.Def_HunterPDE_Regularity_DiffQuotient

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Regularity

/-- Theorem 4.53 (2) of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 125: let `Ω ⊂ ℝⁿ` be open,
`Ω′ ⋐ Ω`, `d = dist(Ω′, ∂Ω) > 0`. If `u ∈ Lᵖ(Ω)` where `1 < p < ∞`, and there is a constant `C`
with `‖D^h u‖_{Lᵖ(Ω′)} ≤ C` for all `0 < |h| < d/2`, then `u ∈ W^{1,p}(Ω′)` and
`‖Du‖_{Lᵖ(Ω′)} ≤ C`. Here `‖D^h u‖_{Lᵖ(Ω′)}` is the `Lᵖ(Ω′)` norm of the Euclidean length
`|D^h u| = (∑ᵢ (D_i^h u)²)^{1/2}` and `‖Du‖_{Lᵖ(Ω′)}` that of `|Du| = (∑ᵢ (∂ᵢu)²)^{1/2}`, the weak
partial derivatives taken on `Ω′`. The distance `d` is modelled as in `diffQuot_eLpNorm_le`: any
`d > 0` with `B(x, d) ⊆ Ω` for all `x ∈ Ω′`. -/
theorem memW_of_diffQuot_bounded {n : ℕ} (Ω Ω' : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (hΩ' : CompactlyContained Ω' Ω) (d : ℝ) (hd : 0 < d)
    (hdist : ∀ x ∈ Ω', Metric.ball x d ⊆ Ω) (p : ℝ≥0∞) (hp : 1 < p) (hp_top : p ≠ ∞)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : MemLp u p (volume.restrict Ω)) (C : ℝ)
    (hC : ∀ h : ℝ, 0 < |h| → |h| < d / 2 →
      eLpNorm (diffQuotNorm h u) p (volume.restrict Ω') ≤ ENNReal.ofReal C) :
    MemW 1 p Ω' u ∧ eLpNorm (Shared.weakGradNorm Ω' u) p (volume.restrict Ω') ≤ ENNReal.ofReal C := by sorry

end HunterPDE.Regularity
