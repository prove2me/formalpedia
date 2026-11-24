-- Prove2me | Theorems.Thm_GlobalTheory_JR_PiSelfDual_trForm_nondegenerate
-- name    : GlobalTheory.JR.PiSelfDual.trForm_nondegenerate
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:35:31.243902+00:00
-- url     : https://prove2.me/theorems/80cf0aa6-008c-4654-8529-ab9dcade54c2
-- title:
--   Pi Self Dual: tr Form nondegenerate
-- statement:
--   The Pi Self Dual construction uses the tr Form nondegenerate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSelfDualPiHaarTraceStarDotProductUnramified.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSelfDualPiHaarTraceStarDotProductUnramified.lean#L64-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSelfDualPiHaarTraceStarDotProductUnramified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.PiSelfDual
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem GlobalTheory.JR.PiSelfDual.trForm_nondegenerate (r : ℕ) : (trForm (F := F) (E := E) r).Nondegenerate := by sorry
