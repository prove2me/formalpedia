-- Prove2me | Theorems.Thm_GilmoreGomory61_CuttingStock_step3_slack_test
-- name    : GilmoreGomory61.CuttingStock.step3_slack_test
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:10:21.790367+00:00
-- url     : https://prove2.me/theorems/caf176e0-b8d2-4333-b61a-664d58dde234
-- title:
--   p. 854, step (3) — a nonbasic surplus variable prices out when its multiplier is negative
-- statement:
--   Let a current feasible basis be fixed. A nonbasic surplus variable in demand row $i$ can participate with the basic columns in a strictly cheaper feasible solution only if the corresponding first-row entry $b_i$ of $B^{-1}$ is negative:
--
--   $$
--   \text{improvement by surplus }i\ \Longrightarrow\ b_i<0.
--   $$
--
--   If all basic values are strictly positive, the converse holds. This is the surplus-column test used before searching for a new cutting activity.
--
--   **Formalization Note** The paper's $(i+1)$st bordered row is the demand row at Lean index $i$. The converse needs nondegeneracy, as acknowledged by the paper's separate zero-ratio procedure.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961), p. 854, step (3)

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Basis

namespace GilmoreGomory61.CuttingStock

/-- Routine step (3): a nonbasic surplus variable prices out exactly for negative multiplier. -/
theorem step3_slack_test {m k : ℕ} (I : Instance m k)
    (β : Fin m → Col I) (hβ : IsFeasibleBasis I β)
    (i : Fin m) (hi : Sum.inr i ∉ Set.range β) :
    (Improves I β (Sum.inr i) → mult I β i < 0) ∧
    (IsNondegenerate I β → mult I β i < 0 → Improves I β (Sum.inr i)) := by sorry

end GilmoreGomory61.CuttingStock
