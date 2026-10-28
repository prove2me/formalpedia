-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_18
-- name    : NQueensComp.NPC.lemma_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:33.540494+00:00
-- url     : https://prove2.me/theorems/5b928b11-f5b1-4934-9b4b-c6b71d31df2c
-- title:
--   Lemma 18 — a solution of M₃ gives a solution of M₄ (Definition 16)
-- statement:
--   Let $M_4=\langle n,C,R,D^-,D^+\rangle$ be an instance of Problem 4 and $M_3$ its image under Definition 16.
--
--   **Lemma 18.** If $S_3$ is a solution to $M_3$, then
--   $$S_4=\{(\alpha-3n+2,\beta)\mid(\alpha,\beta)\in S_3,\ \beta<n\}$$
--   is a solution to $M_4$.
--
--   This is the inverse direction of Lemma 17.
--
--   **Formalization Note** The set is written as $\{q\mid q+(3n-2,0)\in S_3,\ \mathrm{row}(q)<n\}$, which avoids subtracting in $\mathbb N$.
--
--   Differences from the source:
--   - reading: Problem 3 (p. 819) only asks |R| = |C| and α ∉ C, β ∉ R for (α, β) ∈ P → an instance of Problem 3 (and so of Problems 4 and 5) also has C, R ⊆ {0, …, n − 1}; reason: the proofs of Lemmas 11 and 22 use it (“we have α < n₃”, “each max(Cₐ ∪ Rₐ) < nₐ”); without it Theorem 13 is false: ⟨1, {}, {5}, {0}⟩ has the solution {(5, 0)} but Definition 10 outputs a P₂ with (11, 18) and (19, 18) on one row
--   - reading: Problems 3 and 4 take n an integer → board size n ≥ 1; reason: Problem 2 instances are built on n-Queens (Problem 1, n ≥ 1); Definition 10 is undefined at n₃ = 0 (n′ = −1)
--   - encoding: Definition 16: Q_{D⁻} = {(6n − 3 − d, 3n − 1 − 2d)}, Q_{D⁺} = {(2n − 2 − d, n + 2d)}, the shift 3n − 2 and the board 7n − 3 → coordinates computed in ℤ and converted with `Int.toNat`; 3n − 2 and 7n − 3 in ℕ; reason: for valid instances (n ≥ 1, d in range) every value is ≥ 0, so nothing is truncated
--   - encoding: Lemma 18: S₄ = {(α − 3n + 2, β) | (α, β) ∈ S₃, β < n} → S₄ = {q | q + (3n − 2, 0) ∈ S₃, row(q) < n}; reason: the same set on solutions of M₃: every queen of S₃ in a row β < n lies in a column of {c + 3n − 2 | c ∈ C} (the queens of Q_{D⁻} ∪ Q_{D⁺} are in rows ≥ n)
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 827, Lemma 18 (Definition 16)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 18, p. 827: for an instance `M₄` of Problem 4 and `M₃` its image under Definition 16,
if `S₃` is a solution to `M₃` then `S₄ = {(α − 3n + 2, β) | (α, β) ∈ S₃, β < n}` is a solution to
`M₄`. -/
theorem lemma_18 (M : Inst4) (hM : M.Valid) (S₃ : Finset Queen) (hS : (def16 M).IsSol S₃) :
    M.IsSol (lemma18_map M S₃) := by sorry

end NQueensComp.NPC
