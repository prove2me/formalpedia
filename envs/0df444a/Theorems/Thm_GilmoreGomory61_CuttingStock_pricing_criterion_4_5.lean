-- Prove2me | Theorems.Thm_GilmoreGomory61_CuttingStock_pricing_criterion_4_5
-- name    : GilmoreGomory61.CuttingStock.pricing_criterion_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:10:16.871595+00:00
-- url     : https://prove2.me/theorems/61e61f88-16b1-4a73-8a56-d036892be577
-- title:
--   p. 852, (4)–(5) — the entering-column pricing criterion
-- statement:
--   Let $A$ be the invertible coefficient matrix of a current basic feasible solution, $C$ its cost row, and $P$ a nonbasic activity or surplus column of cost $c$. Let $U$ be the unique vector satisfying
--
--   $$
--   A U=P.
--   $$
--
--   If a strictly cheaper feasible solution can be formed using only the basic columns and $P$, then $C\cdot U>c$. Conversely, if every current basic variable is strictly positive, $C\cdot U>c$ yields such an improved solution.
--
--   This is the paper's test (4)–(5), extended to surplus columns as in routine step (2).
--
--   **Formalization Note** The paper later treats a zero minimum ratio as degeneracy (p. 855); strict basic positivity is therefore stated on the sufficient direction. Lean indexes the $m$ coefficient rows from zero.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961), p. 852, (4)–(5); p. 854, step (2)

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Basis

namespace GilmoreGomory61.CuttingStock

/-- The entering-column criterion (4)–(5), with strict basic positivity for its sufficiency. -/
theorem pricing_criterion_4_5 {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β)
    (j : Col I) (hj : j ∉ Set.range β) (U : Fin m → ℝ)
    (hU : Matrix.mulVec (basisMat I β) U = colVec I j) :
    (Improves I β j → colCost I j < ∑ r, costRow I β r * U r) ∧
    (IsNondegenerate I β →
      colCost I j < ∑ r, costRow I β r * U r → Improves I β j) := by sorry

end GilmoreGomory61.CuttingStock
