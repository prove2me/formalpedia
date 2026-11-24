-- Prove2me | Theorems.Thm_GlobalTheory_Phase_VacShape_isMu_mul
-- name    : GlobalTheory.Phase.VacShape.isMu_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:23.741801+00:00
-- url     : https://prove2.me/theorems/f73d9863-6ff4-4163-afdf-f9031115d3e9
-- title:
--   Vac Shape: is Mu mul
-- statement:
--   The Vac Shape construction uses the is Mu mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SelfDualVacuumGaussianShapeRootOfUnityPhases.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SelfDualVacuumGaussianShapeRootOfUnityPhases.lean#L18-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
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
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac

theorem GlobalTheory.Phase.VacShape.isMu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by sorry
