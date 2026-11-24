-- Prove2me | Theorems.Thm_GlobalTheory_Phase_ShapeOps_quad_mul
-- name    : GlobalTheory.Phase.ShapeOps.quad_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:05.098481+00:00
-- url     : https://prove2.me/theorems/d0a78829-b1e9-47da-9fef-bb7199484fc1
-- title:
--   Shape Ops: quad mul
-- statement:
--   The Shape Ops construction uses the quad mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L46-L52

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
variable {M : Type} [AddCommGroup M]

theorem GlobalTheory.Phase.ShapeOps.quad_mul {S : AddSubgroup M} {f g : M → ℂ} (hf : Quad S f) (hg : Quad S g) :
    Quad S (fun x => f x * g x) := by sorry
