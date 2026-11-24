-- Prove2me | Theorems.Thm_GlobalTheory_T_unitaryUnipotentRadicalSplitting_of_leviPart
-- name    : GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:32:12.353476+00:00
-- url     : https://prove2.me/theorems/1f4d81e3-dc63-4fcd-8d70-6a2855cb602b
-- title:
--   T: unitary Unipotent Radical Splitting of levi Part
-- statement:
--   The T construction uses the unitary Unipotent Radical Splitting of levi Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryUnipotentRadicalSplittingOfLeviPartStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryUnipotentRadicalSplittingOfLeviPartStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryUnipotentRadicalSplittingOfLeviPart
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryUnipotentRadicalSplittingOfLeviPartStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart : GlobalTheory.SatakeWeyl.LeviPart → GlobalTheory.SatakeWeyl.UnipSplit := by sorry
