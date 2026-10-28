-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_33
-- name    : NQueensComp.NPC.lemma_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:37.517996+00:00
-- url     : https://prove2.me/theorems/38863423-50ef-4e40-9cf5-7f8ba4fa8151
-- title:
--   Lemma 33 — M₅,c has exactly three solutions, one for each choice of the red variable gadget
-- statement:
--   Let $M_6$ be an instance of Restricted 1-in-3-SAT and $c=\{v_i,v_j,v_k\}$, $i<j<k$, one of its clauses. $M_{5,c}$ is the family of six Problem 4 gadgets $G^0_i,G^0_j,G^0_k,G^1_c,G^2_c,G^3_c$ of Definitions 26–28 and 31. Each $G^0_v=G^0\oplus\delta_v$ has a red solution $\{(0,0),(1,3),(3,2)\}+(\delta_v,0)$ and a blue solution $\{(0,2),(1,0),(3,3)\}+(\delta_v,0)$.
--
--   **Lemma 33.** $M_{5,c}$, as an instance of Problem 5, has exactly three solutions:
--   $$\bigl|\{S_5 : S_5 \text{ solves } M_{5,c}\}\bigr|=3,$$
--   1. in one, $G^0_i$ takes its red solution and $G^0_j,G^0_k$ their blue solutions;
--   2. in a second, $G^0_j$ is red and $G^0_i,G^0_k$ are blue;
--   3. in the third, $G^0_k$ is red and $G^0_i,G^0_j$ are blue.
--
--   Thus the clause gadgets force exactly one variable of each clause to be true, which is what makes the reduction from Restricted 1-in-3-SAT parsimonious.
--
--   **Formalization Note** $M_{5,c}$ is the list `[G⁰ᵢ, G⁰ⱼ, G⁰ₖ, G¹_c, G²_c, G³_c]`, so positions 0, 1, 2 of a solution are the parts on $G^0_i,G^0_j,G^0_k$. The clause is taken inside a fixed instance, because the diagonals $d^x_{v,c}$ depend on the rank of $c$ among the clauses of $v$.
--
--   Differences from the source:
--   - encoding: an instance of Problem 5 is a set M₅ = {M₄,ₐ | 0 ≤ a < |M₅|} and a solution a set S₅ = {S₄,ₐ}; the sum-diagonal condition for any {S₄,ₐ, S₄,b} ⊆ S₅ → an instance is a list [M₄,₀, …, M₄,ₖ₋₁], a solution a list [S₄,₀, …] of the same length, and the sum-diagonal condition is imposed for indices a ≠ b; reason: the paper indexes the family itself; read with a = b the condition would forbid every non-empty solution
--   - encoding: V = {vᵢ}, C = {cᵢ}, an arbitrary order of variables and clauses fixed before the reduction (p. 831); a solution is a truth assignment S₆ : V → {true, false} → variables are natural numbers ordered increasingly (vᵢ is the i-th smallest element of V); the clauses form a duplicate-free list whose order is the clause order; a solution is the set T ⊆ V of true variables; reason: one admissible choice of the fixed orders; assignments V → {true, false} correspond bijectively to subsets T ⊆ V, so counts agree
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 835, Lemma 33

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 33, p. 835: for a clause `c = c_j = {vᵢ, vⱼ, vₖ}` (`i < j < k`) of an instance `M₆`,
the six-gadget family `M₅,c = [G⁰ᵢ, G⁰ⱼ, G⁰ₖ, G¹_c, G²_c, G³_c]` has exactly three solutions: in
one `G⁰ᵢ` takes its red solution and `G⁰ⱼ, G⁰ₖ` their blue ones; in a second `G⁰ⱼ` is red and
`G⁰ᵢ, G⁰ₖ` blue; in the third `G⁰ₖ` is red and `G⁰ᵢ, G⁰ⱼ` blue. -/
theorem lemma_33 (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) :
    _root_.Set.ncard {Ss : List (Finset Queen) | Inst5IsSol (M5c cs j) Ss} = 3 ∧
    (∃ Ss, Inst5IsSol (M5c cs j) Ss ∧
      Ss.getD 0 ∅ = redSol (delta cs (clauseVar cs j 0)) ∧
      Ss.getD 1 ∅ = blueSol (delta cs (clauseVar cs j 1)) ∧
      Ss.getD 2 ∅ = blueSol (delta cs (clauseVar cs j 2))) ∧
    (∃ Ss, Inst5IsSol (M5c cs j) Ss ∧
      Ss.getD 0 ∅ = blueSol (delta cs (clauseVar cs j 0)) ∧
      Ss.getD 1 ∅ = redSol (delta cs (clauseVar cs j 1)) ∧
      Ss.getD 2 ∅ = blueSol (delta cs (clauseVar cs j 2))) ∧
    (∃ Ss, Inst5IsSol (M5c cs j) Ss ∧
      Ss.getD 0 ∅ = blueSol (delta cs (clauseVar cs j 0)) ∧
      Ss.getD 1 ∅ = blueSol (delta cs (clauseVar cs j 1)) ∧
      Ss.getD 2 ∅ = redSol (delta cs (clauseVar cs j 2))) := by sorry

end NQueensComp.NPC
