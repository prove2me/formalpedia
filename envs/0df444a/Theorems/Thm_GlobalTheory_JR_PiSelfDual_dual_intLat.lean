-- Prove2me | Theorems.Thm_GlobalTheory_JR_PiSelfDual_dual_intLat
-- name    : GlobalTheory.JR.PiSelfDual.dual_intLat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:34:55.859259+00:00
-- url     : https://prove2.me/theorems/f228099f-08ef-4f2e-b859-b12f26632535
-- title:
--   Pi Self Dual: dual int Lat
-- statement:
--   The Pi Self Dual construction uses the dual int Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSelfDualPiHaarTraceStarDotProductUnramified.lean#L83-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSelfDualPiHaarTraceStarDotProductUnramified.lean#L83-L107

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

theorem GlobalTheory.JR.PiSelfDual.dual_intLat (r : ℕ) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    {y : Fin r → E | ∀ x ∈ intLat (F := F) (E := E) r, ψ (trForm (F := F) r x y) = 1} =
      ((intLat (F := F) (E := E) r : AddSubgroup (Fin r → E)) : Set (Fin r → E)) := by sorry
