-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_section_eq_zero_of_germ_assPoints
-- name    : GlobalTheory.QCoh.section_eq_zero_of_germ_assPoints
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:46.321797+00:00
-- url     : https://prove2.me/theorems/107a7462-4ff0-4788-be16-c87de99cc877
-- title:
--   QCoh: section eq zero of germ ass Points
-- statement:
--   The QCoh construction uses the section eq zero of germ ass Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L915-L931
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L915-L931

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable [IsLocallyNoetherian X]

theorem GlobalTheory.QCoh.section_eq_zero_of_germ_assPoints [F.IsQuasicoherent] (s : Γ(F, U))
    (h : ∀ x ∈ assPoints F, ∀ hx : x ∈ U, F.presheaf.germ U x hx s = 0) : s = 0 := by sorry
