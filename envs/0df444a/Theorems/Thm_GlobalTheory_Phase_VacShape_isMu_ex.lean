-- Prove2me | Theorems.Thm_GlobalTheory_Phase_VacShape_isMu_ex
-- name    : GlobalTheory.Phase.VacShape.isMu_ex
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:24.230813+00:00
-- url     : https://prove2.me/theorems/d17122ad-6e86-46e7-8a4c-fdceedb76e07
-- title:
--   Vac Shape: is Mu ex
-- statement:
--   The Vac Shape construction uses the is Mu ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SelfDualVacuumGaussianShapeRootOfUnityPhases.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SelfDualVacuumGaussianShapeRootOfUnityPhases.lean#L29-L34

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

theorem GlobalTheory.Phase.VacShape.isMu_ex (q : ℚ) : IsMu (ex q) := by sorry
