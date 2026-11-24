-- Prove2me | Theorems.Thm_GlobalTheory_Phase_ShapeOps_exists_den
-- name    : GlobalTheory.Phase.ShapeOps.exists_den
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:44:56.984042+00:00
-- url     : https://prove2.me/theorems/427fd259-c492-44a8-a32f-c5401115c9c5
-- title:
--   Shape Ops: exists den
-- statement:
--   The Shape Ops construction uses the exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L122-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L122-L134

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

theorem GlobalTheory.Phase.ShapeOps.exists_den (y : Matrix κ ι ℚ) : ∃ N : ℕ, 0 < N ∧ IntM ((N : ℚ) • y) := by sorry
