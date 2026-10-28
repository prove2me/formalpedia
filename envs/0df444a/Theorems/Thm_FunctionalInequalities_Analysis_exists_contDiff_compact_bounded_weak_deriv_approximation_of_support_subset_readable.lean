-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset_readable
-- name    : FunctionalInequalities.Analysis.exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:21.10099+00:00
-- url     : https://prove2.me/theorems/edd33fcd-2ede-42b0-a5c4-34bd95e40e19
-- title:
--   Support-Controlled Smooth Weak-Derivative Approximation
-- statement:
--   This formalizes part of the regularity approximation used in Lemma 2.2 of Letwin (arXiv:2607.24164v1), with a reviewed relation to the cited result.
--
--   Let $n\in\mathbb N$, let $\eta:\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))\to\mathbb R$ be locally integrable and satisfy $\|\eta(x)\|\le C$ for all $x$, and let $a_i$ be functions indexed by $i\in\operatorname{Fin}(n)$. Let $K$ be compact, assume the supports of $\eta$ and all $a_i$ lie in $K$, and assume:
--
--   1. $\varepsilon>0$;
--   2. each $a_i$ is a weak derivative of $\eta$ along the coordinate basis vector $e_i$;
--   3. each $a_i$ belongs to $L^2(\operatorname{vol})$.
--
--   Then there exist a compact set $S\subseteq\operatorname{cthickening}_\varepsilon(K)$ and smooth compactly supported functions $\theta_m$ such that the supports of $\eta$, all $a_i$, every $\theta_m$, and every coordinate derivative of $\theta_m$ lie in $S$; $\|\theta_m(x)\|\le3C$; each derivative is in $L^2$; and
--   $$\|\partial_{e_i}\theta_m-a_i\|_{L^2(\operatorname{vol})}\longrightarrow0.$$
--   Moreover, $\theta_m(x)\to\eta(x)$ for almost every $x$ with respect to volume.
--
--   This is a support- and radius-controlled density statement, valid in every finite dimension including dimension zero.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--             ∀ i : Fin n,
--               Function.support (fun x => fderiv ℝ (θ m) x
--                 (EuclideanSpace.basisFun (Fin n) ℝ i)) ⊆ S ∧
--               MemLp (fun x => fderiv ℝ (θ m) x
--                 (EuclideanSpace.basisFun (Fin n) ℝ i)) 2
--                 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
--           (∀ i : Fin n,
--             Tendsto (fun m => eLpNorm
--               (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x)
--               2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0)) ∧
--           ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
--             Tendsto (fun m => θ m x) atTop (𝓝 (η x))
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
--   Previous: [`exists_contDiff_compact_weak_deriv_approximation`](https://prove2.me/theorems/2972130c-74ad-41b7-aa1b-dec182289761).
--
--   [Source excerpt, lines 418–429](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean#L418-L429) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.2 (Klartag [41]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean#L395-L600 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Approximation`, declaration `FunctionalInequalities.Analysis.exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Approximation

open MeasureTheory Filter Set Metric
open scoped ContDiff Convolution Topology
set_option maxHeartbeats 1200000

theorem FunctionalInequalities.Analysis.exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset_readable {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hηK : Function.support η ⊆ K) (haK : ∀ i : Fin n, Function.support (a i) ⊆ K)
    {ε : ℝ} (hε : 0 < ε)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i)
      (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧ S ⊆ cthickening ε K ∧
      Function.support η ⊆ S ∧ (∀ i : Fin n, Function.support (a i) ⊆ S) ∧
      ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ m : ℕ, ContDiff ℝ ∞ (θ m) ∧ HasCompactSupport (θ m) ∧
          Function.support (θ m) ⊆ S ∧ (∀ x, ‖θ m x‖ ≤ 3 * C) ∧
          ∀ i : Fin n,
            Function.support (fun x => fderiv ℝ (θ m) x
              (EuclideanSpace.basisFun (Fin n) ℝ i)) ⊆ S ∧
            MemLp (fun x => fderiv ℝ (θ m) x
              (EuclideanSpace.basisFun (Fin n) ℝ i)) 2
              (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∀ i : Fin n,
          Tendsto (fun m => eLpNorm
            (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x)
            2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0)) ∧
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          Tendsto (fun m => θ m x) atTop (𝓝 (η x)) := by sorry
