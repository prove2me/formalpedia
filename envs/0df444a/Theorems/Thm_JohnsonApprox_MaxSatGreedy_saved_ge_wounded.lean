-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatGreedy_saved_ge_wounded
-- name    : JohnsonApprox.MaxSatGreedy.saved_ge_wounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:22:13.448461+00:00
-- url     : https://prove2.me/theorems/594f23f9-1d74-467c-9ca5-097568cfce91
-- title:
--   Proof of Theorem 2: each B1 step saves at least as many clauses as it wounds
-- statement:
--   Consider one iteration of algorithm B1, from state $\sigma$ to state $\sigma'$, in which Step 3 chooses the literal $y$. The clauses **saved** in this iteration are $YT$, the clauses of LEFT that contain $y$; they are added to SUB. The clauses **wounded** are those still in LEFT after the iteration that contain the complementary literal $\bar y$: they lose the literal $\bar y$ from LIT without being satisfied. Then
--   $$\bigl|\{C \in \mathrm{LEFT}_{\sigma'} : \bar y \in C\}\bigr| \;\le\; |YT| = \bigl|\{C \in \mathrm{LEFT}_\sigma : y \in C\}\bigr|.$$
--
--   This is the per-iteration accounting on which the upper bound of Theorem 2 rests.
--
--   **Formalization Note** The iteration is `StepWith σ y σ'` from the B1 definition file, which carries Step 3's maximality of $y$ over all literals of LIT. A clause containing both $y$ and $\bar y$ is saved, not wounded.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 262, proof of Theorem 2

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1

namespace JohnsonApprox.MaxSatGreedy

theorem saved_ge_wounded (σ σ' : State) (y : Shared.Literal) (h : StepWith σ y σ') :
    (σ'.LEFT.filter (fun C => y.neg ∈ C)).card ≤ (σ.YT y).card := by sorry

end JohnsonApprox.MaxSatGreedy
