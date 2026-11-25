-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_algebraMap_sections_residueField
-- name    : GlobalTheory.QCoh.algebraMap_sections_residueField
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:45.065811+00:00
-- url     : https://prove2.me/theorems/5606fe85-23f7-58f8-a202-729f2d10f9fd
-- title:
--   QCoh: algebra Map sections residue Field
-- statement:
--   The QCoh construction uses the algebra Map sections residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1015-L1016
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1015-L1016

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

theorem GlobalTheory.QCoh.algebraMap_sections_residueField (x : U) :
    algebraMap Γ(X, U) (X.residueField (x : X)) = (X.evaluation U x x.2).hom := by sorry
