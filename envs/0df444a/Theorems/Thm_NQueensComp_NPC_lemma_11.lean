-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_11
-- name    : NQueensComp.NPC.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:23.49013+00:00
-- url     : https://prove2.me/theorems/f5b3abc6-8105-436d-8ac7-155c27e539a3
-- title:
--   Lemma 11 — a solution of M₂ restricts to a solution of M₃ (Definition 10)
-- statement:
--   Let $M_3=\langle n_3,P_3,C,R\rangle$ be an instance of Problem 3 and $M_2=\langle n_2,P_2\rangle$ its image under Definition 10.
--
--   **Lemma 11.** If $S_2$ is a solution to $M_2$, then
--   $$S_3=\{q\mid q\in S_2,\ \|q\|<n_3\}$$
--   is a solution to $M_3$.
--
--   Together with Lemma 12 this gives the bijection between solutions behind Theorem 13.
--
--   Differences from the source:
--   - reading: Problem 3 (p. 819) only asks |R| = |C| and α ∉ C, β ∉ R for (α, β) ∈ P → an instance of Problem 3 (and so of Problems 4 and 5) also has C, R ⊆ {0, …, n − 1}; reason: the proofs of Lemmas 11 and 22 use it (“we have α < n₃”, “each max(Cₐ ∪ Rₐ) < nₐ”); without it Theorem 13 is false: ⟨1, {}, {5}, {0}⟩ has the solution {(5, 0)} but Definition 10 outputs a P₂ with (11, 18) and (19, 18) on one row
--   - reading: Problems 3 and 4 take n an integer → board size n ≥ 1; reason: Problem 2 instances are built on n-Queens (Problem 1, n ≥ 1); Definition 10 is undefined at n₃ = 0 (n′ = −1)
--   - encoding: Definition 10, step 1: n′ = 2n₃ − 1 when n₃ mod 3 ≠ 2 → ℕ subtraction 2 * n₃ - 1; reason: exact because n₃ ≥ 1
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 825, Lemma 11 (Definition 10, pp. 824–825)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 11, p. 825: for an instance `M₃ = ⟨n₃, P₃, C, R⟩` of Problem 3 and `M₂` its image under
Definition 10, if `S₂` is a solution to `M₂` then `S₃ = {q ∈ S₂ | ‖q‖ < n₃}` is a solution to
`M₃`. -/
theorem lemma_11 (M : Inst3) (hM : M.Valid) (S₂ : Finset Queen) (hS : (def10 M).IsSol S₂) :
    M.IsSol (S₂.filter (fun q => size q < M.n)) := by sorry

end NQueensComp.NPC
