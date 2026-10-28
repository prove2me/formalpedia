-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_fixingOutside_eq_smul_sum_readable
-- name    : FunctionalInequalities.Analysis.Tensor.sum_fixingOutside_eq_smul_sum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:00.623851+00:00
-- url     : https://prove2.me/theorems/18cb6a82-9aad-4b06-823d-b31d65e6a497
-- title:
--   Grouping Supported Permutation Sums by Block Images
-- statement:
--   This is a block-sum identity used in partial symmetrization.
--
--   Let $\Omega$ be finite, let $V$ be a real inner-product space, and let $\rho$ be a permutation representation by linear isometries. Let $A,B,Q\subseteq\Omega$ satisfy $A\subseteq Q\subseteq A\cup B$. For $v\in V$ and a function $T$ on finite subsets, assume that for every permutation $\sigma$ fixing outside $A\cup B$,
--
--   $$
--   \rho(\sigma)v=T(\sigma(A)).
--   $$
--
--   Then
--
--   $$
--   \sum_{\sigma\text{ fixing outside }Q}\rho(\sigma)v
--   =\frac{\#\{\sigma\text{ fixing outside }Q\}}{\binom{|Q|}{|A|}}
--   \sum_{\substack{F\subseteq Q\\|F|=|A|}}T(F).
--   $$
--
--   The identity converts a permutation sum into a sum over subsets, with the common fiber size accounted for by the scalar factor.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_fixingOutside_eq_smul_sum (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) {A B Q : Finset Ω}
--       (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (v : V) (T : Finset Ω → V)
--       (hT : ∀ σ ∈ fixingOutside (A ∪ B), ρ σ v = T (A.image σ)) :
--       ∑ σ ∈ fixingOutside Q, ρ σ v =
--         (((fixingOutside Q).card : ℝ) / (Q.card.choose A.card : ℝ)) •
--           ∑ F ∈ Q.powersetCard A.card, T F
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Supporting theorems: [`card_fiber_eq`](https://prove2.me/theorems/a6caecd1-c605-4b2f-84a7-1d2e29ee0b3f), [`image_mem_powersetCard_of_mem_fixingOutside`](https://prove2.me/theorems/7bccdbf5-5ef4-4af0-ab13-ffd9fefe2d80).
--
--   Previous: [`card_fiber_eq`](https://prove2.me/theorems/a6caecd1-c605-4b2f-84a7-1d2e29ee0b3f) · Next: [`sum_powersetCard_image_eq`](https://prove2.me/theorems/028b041a-5881-4253-b32d-c4e28e699c0f).
--
--   [Source excerpt, lines 809–814](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L809-L814) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L806-L905 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_fixingOutside_eq_smul_sum`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem FunctionalInequalities.Analysis.Tensor.sum_fixingOutside_eq_smul_sum_readable (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) {A B Q : Finset Ω}
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (v : V) (T : Finset Ω → V)
    (hT : ∀ σ ∈ fixingOutside (A ∪ B), ρ σ v = T (A.image σ)) :
    ∑ σ ∈ fixingOutside Q, ρ σ v =
      (((fixingOutside Q).card : ℝ) / (Q.card.choose A.card : ℝ)) •
        ∑ F ∈ Q.powersetCard A.card, T F := by sorry
