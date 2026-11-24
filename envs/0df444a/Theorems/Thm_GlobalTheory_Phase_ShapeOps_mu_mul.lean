-- Prove2me | Theorems.Thm_GlobalTheory_Phase_ShapeOps_mu_mul
-- name    : GlobalTheory.Phase.ShapeOps.mu_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:05.32938+00:00
-- url     : https://prove2.me/theorems/0c9b7ea3-994a-475f-8200-77d0b7a7938e
-- title:
--   Shape Ops: mu mul
-- statement:
--   The Shape Ops construction uses the mu mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsCosetQuadraticPhaseTestFunctionConjCharacterMu.lean#L10-L14

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

theorem GlobalTheory.Phase.ShapeOps.mu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by sorry
