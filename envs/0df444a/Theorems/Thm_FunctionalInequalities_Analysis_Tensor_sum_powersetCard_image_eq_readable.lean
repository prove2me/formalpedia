-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_powersetCard_image_eq_readable
-- name    : FunctionalInequalities.Analysis.Tensor.sum_powersetCard_image_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:00.473838+00:00
-- url     : https://prove2.me/theorems/028b041a-5881-4253-b32d-c4e28e699c0f
-- title:
--   Equivariance of Subset Sums
-- statement:
--   This is an equivariance identity for subset sums.
--
--   Let $\Omega$ be a type, let $V$ be a real inner-product space, let $\rho$ be a permutation representation by linear isometries, let $g$ be a permutation, and let $T$ assign a vector $T(F)$ to each finite subset $F$. Assume
--
--   $$
--   \rho(g)T(F)=T(g(F))
--   $$
--
--   for every finite subset $F$. Then for every finite subset $Q$ and natural number $k$,
--
--   $$
--   \sum_{\substack{F\subseteq g(Q)\\|F|=k}}T(F)
--   =\rho(g)\left(\sum_{\substack{F\subseteq Q\\|F|=k}}T(F)\right).
--   $$
--
--   The result permits subset sums over different blocks to be compared by applying a representing permutation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_powersetCard_image_eq (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) (g : Equiv.Perm Ω)
--       (T : Finset Ω → V) (hT : ∀ F, ρ g (T F) = T (F.image g)) (Q : Finset Ω) (k : ℕ) :
--       ∑ F ∈ (Q.image g).powersetCard k, T F = ρ g (∑ F ∈ Q.powersetCard k, T F)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Previous: [`sum_fixingOutside_eq_smul_sum`](https://prove2.me/theorems/18cb6a82-9aad-4b06-823d-b31d65e6a497) · Next: [`norm_le_choose_mul_norm_blockAverage`](https://prove2.me/theorems/ce21f420-f15e-4872-8c85-4a342b34288d).
--
--   [Source excerpt, lines 910–912](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L910-L912) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L907-L928 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_powersetCard_image_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
omit [Fintype Ω]

theorem FunctionalInequalities.Analysis.Tensor.sum_powersetCard_image_eq_readable (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) (g : Equiv.Perm Ω)
    (T : Finset Ω → V) (hT : ∀ F, ρ g (T F) = T (F.image g)) (Q : Finset Ω) (k : ℕ) :
    ∑ F ∈ (Q.image g).powersetCard k, T F = ρ g (∑ F ∈ Q.powersetCard k, T F) := by sorry
