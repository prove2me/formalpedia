-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_35
-- name    : NQueensComp.NPC.lemma_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:24.674219+00:00
-- url     : https://prove2.me/theorems/9a1a6fef-8ca4-4820-9f0e-f9a500c1db2e
-- title:
--   Lemma 35 — a solution of M₅ gives a 1-in-3 assignment
-- statement:
--   Let $M_6$ be an instance of Restricted 1-in-3-SAT and $M_5$ its image under Definition 31.
--
--   **Lemma 35.** For any solution $S_5=\{S_4(G)\mid G\in M_5\}$ of $M_5$:
--   1. each $S_4(G^0_i)$ is the red or the blue solution of $G^0_i$;
--   2. the assignment $S_6$ with $S_6(v_i)=\mathrm{true}$ iff $S_4(G^0_i)$ is the red solution (and $\mathrm{false}$ iff it is the blue solution) is a solution to $M_6$:
--   $$S_5\ \text{solves}\ M_5\ \Longrightarrow\ S_6\ \text{solves}\ M_6.$$
--
--   This is the inverse direction of Lemma 34.
--
--   **Formalization Note** $G^0_{v}$ sits at position $i$ of the family when $v=v_i$ is the $i$-th smallest variable; $S_6$ is returned as its set of true variables.
--
--   Differences from the source:
--   - encoding: an instance of Problem 5 is a set M₅ = {M₄,ₐ | 0 ≤ a < |M₅|} and a solution a set S₅ = {S₄,ₐ}; the sum-diagonal condition for any {S₄,ₐ, S₄,b} ⊆ S₅ → an instance is a list [M₄,₀, …, M₄,ₖ₋₁], a solution a list [S₄,₀, …] of the same length, and the sum-diagonal condition is imposed for indices a ≠ b; reason: the paper indexes the family itself; read with a = b the condition would forbid every non-empty solution
--   - encoding: V = {vᵢ}, C = {cᵢ}, an arbitrary order of variables and clauses fixed before the reduction (p. 831); a solution is a truth assignment S₆ : V → {true, false} → variables are natural numbers ordered increasingly (vᵢ is the i-th smallest element of V); the clauses form a duplicate-free list whose order is the clause order; a solution is the set T ⊆ V of true variables; reason: one admissible choice of the fixed orders; assignments V → {true, false} correspond bijectively to subsets T ⊆ V, so counts agree
--   - reading: Lemma 35 presupposes that each S₄(G⁰ᵢ) is the red or the blue solution (“S₆ is well defined since …”) → stated as the first conjunct of the conclusion; reason: makes the presupposition of the statement explicit; G⁰ has exactly these two solutions (p. 831)
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 836, Lemma 35

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 35, p. 836: for any solution `S₅` of `M₅` (Definition 31), each `S₄(G⁰ᵢ)` is the red or
the blue solution, and the assignment `S₆(vᵢ) = true` iff `S₄(G⁰ᵢ)` is the red solution solves
`M₆`. -/
theorem lemma_35 (cs : Inst6) (hcs : Inst6Valid cs) (Ss : List (Finset Queen))
    (hS : Inst5IsSol (def31 cs) Ss) :
    (∀ v ∈ vars cs, Ss.getD (varIdx cs v) ∅ = redSol (delta cs v) ∨
      Ss.getD (varIdx cs v) ∅ = blueSol (delta cs v)) ∧
    Inst6IsSol cs (lemma35_map cs Ss) := by sorry

end NQueensComp.NPC
