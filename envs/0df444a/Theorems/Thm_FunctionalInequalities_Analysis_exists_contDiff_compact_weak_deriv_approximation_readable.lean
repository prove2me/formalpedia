-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_contDiff_compact_weak_deriv_approximation_readable
-- name    : FunctionalInequalities.Analysis.exists_contDiff_compact_weak_deriv_approximation_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:24.335291+00:00
-- url     : https://prove2.me/theorems/2972130c-74ad-41b7-aa1b-dec182289761
-- title:
--   Common-Compact-Support Approximation of Two Weak Derivatives
-- statement:
--   This formalizes a supporting density component associated with Lemma 2.4 of Letwin (arXiv:2607.24164v1), with a reviewed relation to the cited result.
--
--   Let $\eta,a,b:\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))\to\mathbb R$ and let $v,w$ be vectors. Assume:
--
--   1. $a$ is a weak derivative of $\eta$ along $v$, and $b$ is a weak derivative of $\eta$ along $w$;
--   2. $\eta$, $a$, and $b$ have compact support;
--   3. $a,b\in L^2(\operatorname{vol})$.
--
--   Then there exist a compact set $S$ and smooth compactly supported functions $\theta_m$ such that the supports of $\eta,a,b,\theta_m$, and the directional derivatives $D\theta_m(\cdot)v,D\theta_m(\cdot)w$ lie in $S$, while both derivatives belong to $L^2(\operatorname{vol})$ and
--   $$\|D\theta_m(\cdot)v-a\|_2\to0,\qquad \|D\theta_m(\cdot)w-b\|_2\to0.$$
--
--   The conclusion is a two-direction compact approximation result and does not assert approximation of all coordinate derivatives.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_contDiff_compact_weak_deriv_approximation {n : ℕ}
--       {η a b : EuclideanSpace ℝ (Fin n) → ℝ} {v w : EuclideanSpace ℝ (Fin n)}
--       (hηv : HasWeakDerivAlong η a v) (hηw : HasWeakDerivAlong η b w)
--       (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
--       (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
--       ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
--         Function.support (η) ⊆ S ∧ Function.support (a) ⊆ S ∧
--         Function.support (b) ⊆ S ∧
--         ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
--           (∀ m, ContDiff ℝ ∞ (θ m) ∧ HasCompactSupport (θ m) ∧
--             Function.support (θ m) ⊆ S ∧
--             Function.support (fun x => fderiv ℝ (θ m) x (v)) ⊆ S ∧
--             Function.support (fun x => fderiv ℝ (θ m) x (w)) ⊆ S ∧
--             MemLp (fun x => fderiv ℝ (θ m) x (v)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--             MemLp (fun x => fderiv ℝ (θ m) x (w)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
--           Tendsto (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (v) - (a) x)
--             2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) ∧
--           Tendsto (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (w) - (b) x)
--             2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Approximation`](https://prove2.me/theorems/55bb7a47-4741-4de8-91f0-25080da6fa69).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`lintegral_enorm_convolution_sq_le`](https://prove2.me/theorems/63807bea-13bd-4a60-93ed-c5b5453cd20a), [`tendsto_eLpNorm_convolution_sub`](https://prove2.me/theorems/3e5007ce-6906-4a04-82a9-55a0bdd821b3), [`fderiv_convolution_eq_of_hasWeakDerivAlong`](https://prove2.me/theorems/21b92288-9077-4db1-9b99-ee62a25b6a04).
--
--   Previous: [`exists_hasWeakDerivAlong_of_forall_cutoff`](https://prove2.me/theorems/db832ddc-e6e0-4365-ace7-102695429d13) · Next: [`exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset`](https://prove2.me/theorems/edd33fcd-2ede-42b0-a5c4-34bd95e40e19).
--
--   [Source excerpt, lines 158–177](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean#L158-L177) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean#L154-L362 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Approximation`, declaration `FunctionalInequalities.Analysis.exists_contDiff_compact_weak_deriv_approximation`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Approximation

open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.exists_contDiff_compact_weak_deriv_approximation_readable {n : ℕ}
    {η a b : EuclideanSpace ℝ (Fin n) → ℝ} {v w : EuclideanSpace ℝ (Fin n)}
    (hηv : HasWeakDerivAlong η a v) (hηw : HasWeakDerivAlong η b w)
    (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
      Function.support (η) ⊆ S ∧ Function.support (a) ⊆ S ∧
      Function.support (b) ⊆ S ∧
      ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ m, ContDiff ℝ ∞ (θ m) ∧ HasCompactSupport (θ m) ∧
          Function.support (θ m) ⊆ S ∧
          Function.support (fun x => fderiv ℝ (θ m) x (v)) ⊆ S ∧
          Function.support (fun x => fderiv ℝ (θ m) x (w)) ⊆ S ∧
          MemLp (fun x => fderiv ℝ (θ m) x (v)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          MemLp (fun x => fderiv ℝ (θ m) x (w)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        Tendsto (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (v) - (a) x)
          2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) ∧
        Tendsto (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (w) - (b) x)
          2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by sorry
