-- Prove2me | Theorems.Thm_NQueensComp_NPC_lemma_30
-- name    : NQueensComp.NPC.lemma_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:32.459025+00:00
-- url     : https://prove2.me/theorems/d47ad557-b462-4301-b589-7bc34f03f13b
-- title:
--   Lemma 30 — inside each clause gadget G¹_c, G²_c, G³_c the possible queens have distinct diagonals
-- statement:
--   Let $M_6$ be an instance of Restricted 1-in-3-SAT and $c=\{v_i,v_j,v_k\}$ ($i<j<k$) one of its clauses, with gadgets $G^1_c,G^2_c,G^3_c$ of Definitions 27 and 28.
--
--   **Lemma 30.** In each of $G^1_c,G^2_c,G^3_c$, with columns $C_i$ and rows $R_i$, the difference-diagonals $\alpha-\beta$ of the positions $(\alpha,\beta)\in C_i\times R_i$ are pairwise distinct, and so are the sum-diagonals $\alpha+\beta$:
--   $$(\alpha,\beta),(\alpha',\beta')\in C_i\times R_i,\ \ \alpha\pm\beta=\alpha'\pm\beta'\ \Longrightarrow\ (\alpha,\beta)=(\alpha',\beta').$$
--
--   So inside a clause gadget two queens can only clash along a row or a column, which reduces the count of its solutions to a choice of rows for its columns.
--
--   **Formalization Note** The clause is `cs.getD j ∅` for an index `j` below the length of the clause list; its variables $v_i<v_j<v_k$ are its elements in increasing order.
--
--   Differences from the source:
--   - encoding: V = {vᵢ}, C = {cᵢ}, an arbitrary order of variables and clauses fixed before the reduction (p. 831); a solution is a truth assignment S₆ : V → {true, false} → variables are natural numbers ordered increasingly (vᵢ is the i-th smallest element of V); the clauses form a duplicate-free list whose order is the clause order; a solution is the set T ⊆ V of true variables; reason: one admissible choice of the fixed orders; assignments V → {true, false} correspond bijectively to subsets T ⊆ V, so counts agree
-- source:
--   Gent, Jefferson & Nightingale, Complexity of n-Queens Completion, J. Artif. Intell. Res. 59 (2017), p. 834, Lemma 30

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

namespace NQueensComp.NPC

/-- Lemma 30, p. 834: within each of `G¹_c, G²_c, G³_c` (columns `Cᵢ`, rows `Rᵢ`), the
difference-diagonals `α − β` with `α ∈ Cᵢ, β ∈ Rᵢ` are all distinct, and so are the sum-diagonals
`α + β`. -/
theorem lemma_30 (cs : Inst6) (hcs : Inst6Valid cs) (j : ℕ) (hj : j < cs.length) :
    ∀ G ∈ [G1 cs j, G2 cs j, G3 cs j],
      (∀ p ∈ G.C ×ˢ G.R, ∀ p' ∈ G.C ×ˢ G.R, diffDiag p = diffDiag p' → p = p') ∧
      (∀ p ∈ G.C ×ˢ G.R, ∀ p' ∈ G.C ×ˢ G.R, sumDiag p = sumDiag p' → p = p') := by sorry

end NQueensComp.NPC
