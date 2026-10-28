-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_17
-- name    : NQueensComp.NPC.lemma_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:26.603182+00:00
-- url     : https://prove2.me/theorems/fa556d06-966d-4861-9020-2125a8010b58
-- title:
--   Lemma 17 — a solution of M₄ gives a solution of M₃ (Definition 16)
-- statement:
--   Let $M_4=\langle n,C,R,D^-,D^+\rangle$ be an instance of Problem 4 and $M_3$ its image under Definition 16, with $Q_{D^-}=\{(6n-3-d,3n-1-2d)\mid d\in D^-\}$ and $Q_{D^+}=\{(2n-2-d,n+2d)\mid d\in D^+\}$.
--
--   **Lemma 17.** If $S_4$ is a solution to $M_4$, then
--   $$S_3=\bigl(S_4+(3n-2,0)\bigr)\cup Q_{D^-}\cup Q_{D^+}$$
--   is a solution to $M_3$.
--
--   Together with Lemma 18 this gives the bijection between solutions behind Theorem 19.
--
--   Differences from the source:
--   - reading: Problem 3 (p. 819) only asks |R| = |C| and α ∉ C, β ∉ R for (α, β) ∈ P → an instance of Problem 3 (and so of Problems 4 and 5) also has C, R ⊆ {0, …, n − 1}; reason: the proofs of Lemmas 11 and 22 use it (“we have α < n₃”, “each max(Cₐ ∪ Rₐ) < nₐ”); without it Theorem 13 is false: ⟨1, {}, {5}, {0}⟩ has the solution {(5, 0)} but Definition 10 outputs a P₂ with (11, 18) and (19, 18) on one row
--   - reading: Problems 3 and 4 take n an integer → board size n ≥ 1; reason: Problem 2 instances are built on n-Queens (Problem 1, n ≥ 1); Definition 10 is undefined at n₃ = 0 (n′ = −1)
--   - encoding: Definition 16: Q_{D⁻} = {(6n − 3 − d, 3n − 1 − 2d)}, Q_{D⁺} = {(2n − 2 − d, n + 2d)}, the shift 3n − 2 and the board 7n − 3 → coordinates computed in ℤ and converted with `Int.toNat`; 3n − 2 and 7n − 3 in ℕ; reason: for valid instances (n ≥ 1, d in range) every value is ≥ 0, so nothing is truncated
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 827, Lemma 17 (Definition 16)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 17, p. 827: for an instance `M₄ = ⟨n, C, R, D⁻, D⁺⟩` of Problem 4 and `M₃` its image
under Definition 16, if `S₄` is a solution to `M₄` then `S₃ = (S₄ + (3n − 2, 0)) ∪ Q_{D⁻} ∪ Q_{D⁺}`
is a solution to `M₃`. -/
theorem lemma_17 (M : Inst4) (hM : M.Valid) (S₄ : Finset Queen) (hS : M.IsSol S₄) :
    (def16 M).IsSol (lemma17_map M S₄) := by sorry

end NQueensComp.NPC
