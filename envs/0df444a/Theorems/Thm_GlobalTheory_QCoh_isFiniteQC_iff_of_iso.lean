-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isFiniteQC_iff_of_iso
-- name    : GlobalTheory.QCoh.isFiniteQC_iff_of_iso
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:36.684897+00:00
-- url     : https://prove2.me/theorems/8c1aa1fb-5db9-59a8-87ff-daa40ee08296
-- title:
--   QCoh: is Finite QC iff of iso
-- statement:
--   The QCoh construction uses the is Finite QC iff of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L108-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L108-L109

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
attribute [instance 100] IsFiniteQC.isQuasicoherent

theorem GlobalTheory.QCoh.isFiniteQC_iff_of_iso (e : F ≅ G) : IsFiniteQC F ↔ IsFiniteQC G := by sorry
