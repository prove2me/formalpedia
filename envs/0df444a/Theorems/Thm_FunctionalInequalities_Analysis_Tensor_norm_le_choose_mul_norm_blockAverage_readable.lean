-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_le_choose_mul_norm_blockAverage_readable
-- name    : FunctionalInequalities.Analysis.Tensor.norm_le_choose_mul_norm_blockAverage_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:00.32065+00:00
-- url     : https://prove2.me/theorems/ce21f420-f15e-4872-8c85-4a342b34288d
-- title:
--   Binomial Partial Symmetrization Bound
-- statement:
--   Let $\Omega$ be finite, let $V$ be a real inner-product space, and let $\rho$ be a permutation representation by linear isometries. Let $A,B,Q\subseteq\Omega$ and $d\in\mathbb N$ satisfy:
--   1. $|A|=d$ and $|B|=2d$.
--   2. $A$ and $B$ are disjoint.
--   3. $A\subseteq Q\subseteq A\cup B$.
--   4. $|Q|=2d$.
--   5. $v\in V$ is invariant under permutations fixing outside $A$ and under permutations fixing outside $B$.
--
--   Then
--
--   $$
--   \|v\|\le \binom{2d}{d}\,\|\operatorname{blockAverage}(\rho,Q,v)\|.
--   $$
--
--   This is the stronger binomial-factor version of the partial symmetrization estimate.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_le_choose_mul_norm_blockAverage (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V))
--       {A B Q : Finset Ω} {d : ℕ} (hA : A.card = d) (hB : B.card = 2 * d) (hAB : Disjoint A B)
--       (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (hQc : Q.card = 2 * d) (v : V)
--       (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v) :
--       ‖v‖ ≤ ((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Supporting theorems: [`apply_eq_of_image_eq`](https://prove2.me/theorems/d208003e-b651-43c5-a3e4-e5c080e8a606), [`exists_mem_fixingOutside_image_eq`](https://prove2.me/theorems/14b5df8e-d013-4b01-a20c-a437a2621fc7), [`sum_fixingOutside_eq_smul_sum`](https://prove2.me/theorems/18cb6a82-9aad-4b06-823d-b31d65e6a497), [`sum_norm_sq_le_sum_norm_sq_sum_subset`](https://prove2.me/theorems/2747bdb8-2573-4a48-9d87-e05edbda390e), [`sum_powersetCard_image_eq`](https://prove2.me/theorems/028b041a-5881-4253-b32d-c4e28e699c0f).
--
--   Previous: [`sum_powersetCard_image_eq`](https://prove2.me/theorems/028b041a-5881-4253-b32d-c4e28e699c0f) · Next: [`norm_le_four_pow_mul_norm_blockAverage`](https://prove2.me/theorems/9105d9b3-66ee-4045-906c-b84556304fa1).
--
--   [Source excerpt, lines 945–949](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L945-L949) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Lemma 2.2 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 9, in orthogonal-representation form.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L944-L1111 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.norm_le_choose_mul_norm_blockAverage`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem FunctionalInequalities.Analysis.Tensor.norm_le_choose_mul_norm_blockAverage_readable (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V))
    {A B Q : Finset Ω} {d : ℕ} (hA : A.card = d) (hB : B.card = 2 * d) (hAB : Disjoint A B)
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (hQc : Q.card = 2 * d) (v : V)
    (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v) :
    ‖v‖ ≤ ((2 * d).choose d : ℝ) * ‖blockAverage ρ Q v‖ := by sorry
