-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_21
-- name    : NQueensComp.NPC.lemma_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:35.035989+00:00
-- url     : https://prove2.me/theorems/0198345a-3519-4fb9-8363-66e4dcc81fcc
-- title:
--   Lemma 21 — a solution of M₅ gives a solution of M₄ (corrected: D⁺ of Definition 20 ends at 2n − 2)
-- statement:
--   Let $M_5=\{M_{4,a}\mid 0\le a<k\}$, $k\ge1$, be an instance of Problem 5 and $M_4$ its image under Definition 20, with offsets $\alpha_a=2n'a$, $\beta_a=2n'(k-1-a)$.
--
--   **Lemma 21.** If $S_5=\{S_{4,a}\mid 0\le a<k\}$ is a solution to $M_5$, then
--   $$S_4=\bigcup_{0\le a<k}\bigl(S_{4,a}+(\alpha_a,\beta_a)\bigr)$$
--   is a solution to $M_4$.
--
--   Together with Lemma 22 this gives the bijection between solutions behind Theorem 23.
--
--   **Formalization Note** $M_4$ is the corrected Definition 20 of the definition module.
--
--   Differences from the source:
--   - encoding: an instance of Problem 5 is a set M₅ = {M₄,ₐ | 0 ≤ a < |M₅|} and a solution a set S₅ = {S₄,ₐ}; the sum-diagonal condition for any {S₄,ₐ, S₄,b} ⊆ S₅ → an instance is a list [M₄,₀, …, M₄,ₖ₋₁], a solution a list [S₄,₀, …] of the same length, and the sum-diagonal condition is imposed for indices a ≠ b; reason: the paper indexes the family itself; read with a = b the condition would forbid every non-empty solution
--   - reading: Problem 3 (p. 819) only asks |R| = |C| and α ∉ C, β ∉ R for (α, β) ∈ P → an instance of Problem 3 (and so of Problems 4 and 5) also has C, R ⊆ {0, …, n − 1}; reason: the proofs of Lemmas 11 and 22 use it (“we have α < n₃”, “each max(Cₐ ∪ Rₐ) < nₐ”); without it Theorem 13 is false: ⟨1, {}, {5}, {0}⟩ has the solution {(5, 0)} but Definition 10 outputs a P₂ with (11, 18) and (19, 18) on one row
--   - reading: Lemmas 21 and 22 for an instance M₅ of Problem 5 → the family is non-empty (k ≥ 1); reason: Definition 20 is defined only for k ≥ 1 (n′ = max of the nₐ); the k = 0 output is the correction of Theorem 23 and is outside the lemmas
--   - correction: Definition 20: D⁺ = {0, …, 2n′(k−1) − 1} ∪ {2n′k, …, 4n′k − 2} → D⁺ = {0, …, 2n′(k−1) − 1} ∪ {2n′k, …, 2n − 2} with n = n′(2k − 1); reason: Problem 4 requires D⁺ ⊆ {0, …, 2n − 2} and 2n − 2 = 4n′k − 2n′ − 2, so the printed set is never a valid D⁺ (k = 1, n′ = 2: D⁺ = {4, 5, 6} ⊄ {0, 1, 2}); the dropped values are sum-diagonals no square of the board has, so every solution set is unchanged
--   - reading: Problems 3 and 4 take n an integer → board size n ≥ 1; reason: Problem 2 instances are built on n-Queens (Problem 1, n ≥ 1); Definition 10 is undefined at n₃ = 0 (n′ = −1)
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 830, Lemma 21 (Definition 20, pp. 828–829)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 21, p. 830: for a non-empty instance `M₅ = {M₄,ₐ | 0 ≤ a < k}` of Problem 5 and `M₄`
its image under Definition 20, if `S₅ = {S₄,ₐ}` is a solution to `M₅` then
`S₄ = ⋃_{0≤a<k} (S₄,ₐ + (αₐ, βₐ))` is a solution to `M₄`. -/
theorem lemma_21 (Ms : Inst5) (hMs : Inst5Valid Ms) (hk : Ms ≠ []) (Ss : List (Finset Queen))
    (hS : Inst5IsSol Ms Ss) : (def20 Ms).IsSol (lemma21_map Ms Ss) := by sorry

end NQueensComp.NPC
