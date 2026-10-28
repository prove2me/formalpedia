-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_34
-- name    : NQueensComp.NPC.lemma_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:30.36+00:00
-- url     : https://prove2.me/theorems/e591eab8-42c6-4894-bd76-5a44ace1d71d
-- title:
--   Lemma 34 — a 1-in-3 assignment gives a solution of M₅
-- statement:
--   Let $M_6$ be an instance of Restricted 1-in-3-SAT and $M_5$ its image under Definition 31.
--
--   **Lemma 34.** If the truth assignment $S_6$ solves $M_6$, then $S_5=\{S_4(G)\mid G\in M_5\}$ is a solution to $M_5$, where $S_4(G^0_i)$ is the red solution if $S_6(v_i)=\mathrm{true}$ and the blue solution otherwise, and $S_4(G^1_c),S_4(G^2_c),S_4(G^3_c)$ are chosen as in the proof of Lemma 33 according to which variable of $c$ is true:
--   $$S_6\ \text{solves}\ M_6\ \Longrightarrow\ S_5\ \text{solves}\ M_5.$$
--
--   Together with Lemma 35 this gives the bijection between solutions behind Theorem 36.
--
--   **Formalization Note** $S_6$ is given by its set $T$ of true variables. The clause-gadget parts are the explicit table of the definition module (`clauseSols`), which writes out the three cases of the proof of Lemma 33.
--
--   Differences from the source:
--   - encoding: an instance of Problem 5 is a set M₅ = {M₄,ₐ | 0 ≤ a < |M₅|} and a solution a set S₅ = {S₄,ₐ}; the sum-diagonal condition for any {S₄,ₐ, S₄,b} ⊆ S₅ → an instance is a list [M₄,₀, …, M₄,ₖ₋₁], a solution a list [S₄,₀, …] of the same length, and the sum-diagonal condition is imposed for indices a ≠ b; reason: the paper indexes the family itself; read with a = b the condition would forbid every non-empty solution
--   - encoding: V = {vᵢ}, C = {cᵢ}, an arbitrary order of variables and clauses fixed before the reduction (p. 831); a solution is a truth assignment S₆ : V → {true, false} → variables are natural numbers ordered increasingly (vᵢ is the i-th smallest element of V); the clauses form a duplicate-free list whose order is the clause order; a solution is the set T ⊆ V of true variables; reason: one admissible choice of the fixed orders; assignments V → {true, false} correspond bijectively to subsets T ⊆ V, so counts agree
--   - encoding: S₄(G¹_c), S₄(G²_c), S₄(G³_c) “set as in the proof of Lemma 33”, which gives the case of vᵢ red and omits the cases vⱼ, vₖ red (p. 836) → the explicit table `clauseSols` for all three cases; reason: the omitted cases are derived by the rules the proof states; the table was checked by enumerating all solutions of M₅,c
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 836, Lemma 34 (with the proof of Lemma 33, p. 835)

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 34, p. 836: if the truth assignment with true set `T` solves `M₆`, then `S₅` is a
solution to `M₅` (Definition 31), where `S₄(G⁰ᵢ)` is the red solution iff `vᵢ ∈ T` and the blue one
otherwise, and `S₄(G¹_c), S₄(G²_c), S₄(G³_c)` are as in the proof of Lemma 33. -/
theorem lemma_34 (cs : Inst6) (hcs : Inst6Valid cs) (T : Finset ℕ) (hT : Inst6IsSol cs T) :
    Inst5IsSol (def31 cs) (lemma34_map cs T) := by sorry

end NQueensComp.NPC
