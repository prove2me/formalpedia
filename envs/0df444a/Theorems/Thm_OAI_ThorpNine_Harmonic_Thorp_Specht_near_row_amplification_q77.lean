-- Prove2me | Theorems.Thm_OAI_ThorpNine_Harmonic_Thorp_Specht_near_row_amplification_q77
-- name    : OAI.ThorpNine.Harmonic.Thorp.Specht.near_row_amplification_q77
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:57:58.260673+00:00
-- url     : https://prove2.me/theorems/5c048b00-b60d-405e-a21a-596dd30203a9
-- title:
--   OAI.ThorpNine.Harmonic.Thorp.Specht.near_row_amplification_q77: intermediate lemma from OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ThorpNine.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Optimal logarithmic mixing of the Thorp shuffle (routing densities)*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ThorpNine.Harmonic.Thorp.Specht.near_row_amplification` of [lean/OAI/Probability/ThorpRouting/Harmonic/InsertionPerm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Harmonic/InsertionPerm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ThorpNine.Harmonic.Thorp.Specht`, with `open scoped BigOperators Classical`, `open UnitaryFinite DimensionEstimates Filter`):
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
--   **Definitions.** The statement is written with `OAI.ThorpNine.Harmonic.Thorp.densityConstant`, `OAI.ThorpNine.Harmonic.Thorp.UnitaryFinite.fixedSpace` and `OAI.ThorpNine.Harmonic.Thorp.UnitaryFinite.tupleAction` (definitions bundle `OAIQ077T001` of this split); `OAI.ThorpNine.Harmonic.Thorp.BenesCoins`, `OAI.ThorpNine.Harmonic.Thorp.Card`, `OAI.ThorpNine.Harmonic.Thorp.SwitchIndex`, `OAI.ThorpNine.Harmonic.Thorp.instDecidableEqSwitchIndex`, `OAI.ThorpNine.Harmonic.Thorp.instFintypeSwitchIndex`, `OAI.ThorpNine.Harmonic.Thorp.palindromePerm`, `OAI.ThorpNine.Harmonic.Thorp.PermutationHilbert.H`, `OAI.ThorpNine.Harmonic.Thorp.Specht.Cell`, `OAI.ThorpNine.Harmonic.Thorp.Specht.Tabloid`, `OAI.ThorpNine.Harmonic.Thorp.Specht.hilbertSpace`, `OAI.ThorpNine.Harmonic.Thorp.Specht.instFintypeTabloid`, `OAI.ThorpNine.Harmonic.Thorp.Specht.relabelledUnitary`, `OAI.ThorpNine.Harmonic.Thorp.Specht.rowIndex` and `OAI.ThorpNine.Harmonic.Thorp.UnitaryFinite.sampleOperator` (the published bundle `Def_ThorpRouting`).
--
--   **Used by.** The proof of `OAI.ThorpNine.Harmonic.Thorp.Specht.spectral_regimes_q77` of this split imports it.
-- source:
--   OpenAI, Optimal logarithmic mixing of the Thorp shuffle (routing densities), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Routing-densities-and-representation-contraction-for-Thorp-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ThorpRouting/Harmonic/InsertionPerm.lean (declaration OAI.ThorpNine.Harmonic.Thorp.Specht.near_row_amplification)

import Mathlib
import Definitions.Def_ThorpRouting
import Definitions.Def_OAIQ077T001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ThorpNine.Harmonic

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

end ThorpNine.Harmonic

end OAI
end
