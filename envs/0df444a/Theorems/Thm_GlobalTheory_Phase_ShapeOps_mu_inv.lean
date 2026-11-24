-- Prove2me | Theorems.Thm_GlobalTheory_Phase_ShapeOps_mu_inv
-- name    : GlobalTheory.Phase.ShapeOps.mu_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:45:00.851528+00:00
-- url     : https://prove2.me/theorems/8f6b705e-514d-421b-97be-c44ff5e22cae
-- title:
--   Shape Ops: mu inv
-- statement:
--   The Shape Ops construction uses the mu inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L16-L18

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

theorem GlobalTheory.Phase.ShapeOps.mu_inv {a : ℂ} (ha : IsMu a) : IsMu a⁻¹ := by sorry
