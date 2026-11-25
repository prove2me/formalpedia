-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_algebraMap_residueField
-- name    : GlobalTheory.QCoh.algebraMap_residueField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:43.608849+00:00
-- url     : https://prove2.me/theorems/825740f9-0464-5454-891e-529290990ae3
-- title:
--   QCoh: algebra Map residue Field
-- statement:
--   The QCoh construction uses the algebra Map residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1009-L1010
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1009-L1010

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

theorem GlobalTheory.QCoh.algebraMap_residueField (x : X) :
    algebraMap (X.presheaf.stalk x) (X.residueField x) = (X.residue x).hom := by sorry
