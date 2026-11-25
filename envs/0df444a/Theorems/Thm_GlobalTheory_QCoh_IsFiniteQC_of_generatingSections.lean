-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_of_generatingSections
-- name    : GlobalTheory.QCoh.IsFiniteQC.of_generatingSections
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:04:22.721316+00:00
-- url     : https://prove2.me/theorems/696b68ce-f121-4fc5-b1c9-261ec278c580
-- title:
--   Is Finite QC: of generating Sections
-- statement:
--   The Is Finite QC construction uses the of generating Sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L341-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L341-L344

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
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.QCoh.IsFiniteQC.of_generatingSections [F.IsQuasicoherent] (σ : F.GeneratingSections)
    [σ.IsFiniteType] : IsFiniteQC F := by sorry
