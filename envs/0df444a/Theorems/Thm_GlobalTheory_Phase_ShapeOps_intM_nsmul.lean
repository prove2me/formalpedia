-- Prove2me | Theorems.Thm_GlobalTheory_Phase_ShapeOps_intM_nsmul
-- name    : GlobalTheory.Phase.ShapeOps.intM_nsmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:44:38.691998+00:00
-- url     : https://prove2.me/theorems/cf54cc3b-c041-47c4-83ca-dc7b41fbaff5
-- title:
--   Shape Ops: int M nsmul
-- statement:
--   The Shape Ops construction uses the int M nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L118-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsCosetQuadraticPhaseTestFunctionConjCharacterMu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ShapeOps
variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.Phase.ShapeOps.intM_nsmul (N : ℕ) {z : Matrix κ ι ℚ} (hz : IntM z) : IntM ((N : ℚ) • z) := by sorry
