-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_image_mem_powersetCard_of_mem_fixingOutside_readable
-- name    : FunctionalInequalities.Analysis.Tensor.image_mem_powersetCard_of_mem_fixingOutside_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:57.350995+00:00
-- url     : https://prove2.me/theorems/7bccdbf5-5ef4-4af0-ab13-ffd9fefe2d80
-- title:
--   Images of Subsets Under Supported Permutations
-- statement:
--   This is a finite-set invariance lemma.
--
--   Let $A,Q\subseteq\Omega$ be finite subsets with $A\subseteq Q$. If a permutation $\sigma$ fixes every point outside $Q$, then the image $\sigma(A)$ is a subset of $Q$ with the same cardinality as $A$:
--
--   $$
--   \sigma(A)\in\{F\subseteq Q:|F|=|A|\}.
--   $$
--
--   This identifies the possible images of $A$ when permutation sums are restricted to permutations supported in $Q$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem image_mem_powersetCard_of_mem_fixingOutside {A Q : Finset Ω} (hAQ : A ⊆ Q)
--       {σ : Equiv.Perm Ω} (hσ : σ ∈ fixingOutside Q) : A.image σ ∈ Q.powersetCard A.card
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Previous: [`apply_eq_of_image_eq`](https://prove2.me/theorems/d208003e-b651-43c5-a3e4-e5c080e8a606) · Next: [`card_fiber_eq`](https://prove2.me/theorems/a6caecd1-c605-4b2f-84a7-1d2e29ee0b3f).
--
--   [Source excerpt, lines 717–718](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L717-L718) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L716-L730 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.image_mem_powersetCard_of_mem_fixingOutside`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem FunctionalInequalities.Analysis.Tensor.image_mem_powersetCard_of_mem_fixingOutside_readable {A Q : Finset Ω} (hAQ : A ⊆ Q)
    {σ : Equiv.Perm Ω} (hσ : σ ∈ fixingOutside Q) : A.image σ ∈ Q.powersetCard A.card := by sorry
