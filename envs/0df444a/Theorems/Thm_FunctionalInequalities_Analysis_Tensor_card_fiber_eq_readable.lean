-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_fiber_eq_readable
-- name    : FunctionalInequalities.Analysis.Tensor.card_fiber_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:01.041505+00:00
-- url     : https://prove2.me/theorems/a6caecd1-c605-4b2f-84a7-1d2e29ee0b3f
-- title:
--   Equal Fiber Cardinalities for Block Images
-- statement:
--   This is a finite-combinatorial fiber-counting lemma.
--
--   Let $\Omega$ be finite and let $A,Q,F,F'\subseteq\Omega$ be finite subsets. Assume that $F$ and $F'$ are both $|A|$-element subsets of $Q$. Then the two fibers of the map $\sigma\mapsto\sigma(A)$, restricted to permutations fixing every point outside $Q$, have equal cardinality:
--
--   $$
--   \#\{\sigma\text{ fixing outside }Q:\sigma(A)=F\}
--   =
--   \#\{\sigma\text{ fixing outside }Q:\sigma(A)=F'\}.
--   $$
--
--   This uniformity is used when grouping permutation sums by the image of $A$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem card_fiber_eq {A Q : Finset Ω} {F F' : Finset Ω}
--       (hF : F ∈ Q.powersetCard A.card) (hF' : F' ∈ Q.powersetCard A.card) :
--       ((fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F).card =
--         ((fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F').card
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Supporting theorems: [`exists_mem_fixingOutside_image_eq`](https://prove2.me/theorems/14b5df8e-d013-4b01-a20c-a437a2621fc7).
--
--   Previous: [`image_mem_powersetCard_of_mem_fixingOutside`](https://prove2.me/theorems/7bccdbf5-5ef4-4af0-ab13-ffd9fefe2d80) · Next: [`sum_fixingOutside_eq_smul_sum`](https://prove2.me/theorems/18cb6a82-9aad-4b06-823d-b31d65e6a497).
--
--   [Source excerpt, lines 771–774](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L771-L774) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L769-L804 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.card_fiber_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem FunctionalInequalities.Analysis.Tensor.card_fiber_eq_readable {A Q : Finset Ω} {F F' : Finset Ω}
    (hF : F ∈ Q.powersetCard A.card) (hF' : F' ∈ Q.powersetCard A.card) :
    ((fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F).card =
      ((fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F').card := by sorry
