-- Prove2me | Theorems.Thm_GlobalTheory_Phase_ShapeOps_shape_chr
-- name    : GlobalTheory.Phase.ShapeOps.shape_chr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:45:10.140669+00:00
-- url     : https://prove2.me/theorems/2f59c1d4-ec55-4eba-9c41-795ddc486190
-- title:
--   Shape Ops: shape chr
-- statement:
--   The Shape Ops construction uses the shape chr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L173-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L173-L182

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

theorem GlobalTheory.Phase.ShapeOps.shape_chr {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (y : Matrix κ ι ℚ) :
    Shape (fun x => φ x * chr y x) := by sorry
