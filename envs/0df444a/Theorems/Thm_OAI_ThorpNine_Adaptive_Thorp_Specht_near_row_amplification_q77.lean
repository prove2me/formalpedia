-- Prove2me | Theorems.Thm_OAI_ThorpNine_Adaptive_Thorp_Specht_near_row_amplification_q77
-- name    : OAI.ThorpNine.Adaptive.Thorp.Specht.near_row_amplification_q77
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:55:27.451166+00:00
-- url     : https://prove2.me/theorems/2d54161b-5433-4cb2-a809-2f162199bb25
-- title:
--   OAI.ThorpNine.Adaptive.Thorp.Specht.near_row_amplification_q77: intermediate lemma from OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpNine.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal logarithmic mixing of the Thorp shuffle (routing densities)*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThorpNine.Adaptive.Thorp.Specht.near_row_amplification` of [lean/OAI/Probability/ThorpRouting/Adaptive/InsertionPerm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Adaptive/InsertionPerm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThorpNine.Adaptive.Thorp.Specht`, with `open scoped BigOperators Classical`, `open UnitaryFinite DimensionEstimates Filter`):
--
--   ```lean
--   lemma near_row_amplification_q77 (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ)
--       {k : ℕ} (f : Fin k ↪ Card d) (hk : 0<k)
--       (hm : 0<Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e))) :
--       ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ ≤
--         Real.exp (densityConstant*(k:ℝ)*((k:ℝ)/(2:ℝ)^d)^(1/512:ℝ))*
--           (Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))^(-(1/1000:ℝ))+
--         Real.sqrt ((Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))/
--           (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)):ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ThorpNine.Adaptive.Thorp.BenesCoins`, `OAI.ThorpNine.Adaptive.Thorp.densityConstant`, `OAI.ThorpNine.Adaptive.Thorp.palindromePerm`, `OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.fixedSpace` and `OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.tupleAction` (definitions bundle `OAIQ077T000` of this split); `OAI.ThorpNine.Adaptive.Thorp.Card`, `OAI.ThorpNine.Adaptive.Thorp.SwitchIndex`, `OAI.ThorpNine.Adaptive.Thorp.instDecidableEqSwitchIndex`, `OAI.ThorpNine.Adaptive.Thorp.instFintypeSwitchIndex`, `OAI.ThorpNine.Adaptive.Thorp.PermutationHilbert.H`, `OAI.ThorpNine.Adaptive.Thorp.Specht.Cell`, `OAI.ThorpNine.Adaptive.Thorp.Specht.Tabloid`, `OAI.ThorpNine.Adaptive.Thorp.Specht.hilbertSpace`, `OAI.ThorpNine.Adaptive.Thorp.Specht.instFintypeTabloid`, `OAI.ThorpNine.Adaptive.Thorp.Specht.relabelledUnitary`, `OAI.ThorpNine.Adaptive.Thorp.Specht.rowIndex` and `OAI.ThorpNine.Adaptive.Thorp.UnitaryFinite.sampleOperator` (the published bundle `Def_ThorpRouting`).
--
--   **Used by.** The proof of `OAI.ThorpNine.Adaptive.Thorp.Specht.spectral_regimes_q77` of this split imports it.
-- source:
--   OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Adaptive/InsertionPerm.lean (declaration OAI.ThorpNine.Adaptive.Thorp.Specht.near_row_amplification)

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Adaptive

namespace Thorp.Specht
open scoped BigOperators Classical
open UnitaryFinite DimensionEstimates Filter

lemma near_row_amplification_q77 (d : ℕ) (μ : YoungDiagram) (e : Card d ≃ Cell μ)
    {k : ℕ} (f : Fin k ↪ Card d) (hk : 0<k)
    (hm : 0<Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e))) :
    ‖sampleOperator (V := hilbertSpace μ) (relabelledUnitary μ e) (palindromePerm d)‖ ≤
      Real.exp (densityConstant*(k:ℝ)*((k:ℝ)/(2:ℝ)^d)^(1/512:ℝ))*
        (Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))^(-(1/1000:ℝ))+
      Real.sqrt ((Real.exp (Real.log (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)))/2))/
        (Module.finrank ℂ (fixedSpace (V := hilbertSpace μ) tupleAction f (relabelledUnitary μ e)):ℝ)) := by
  sorry

end Thorp.Specht

end ThorpNine.Adaptive

end OAI
end
