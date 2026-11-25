-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_isFinitePresentation
-- name    : GlobalTheory.QCoh.IsFiniteQC.isFinitePresentation
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:02:17.855224+00:00
-- url     : https://prove2.me/theorems/e5913b06-0ce3-5b97-b37d-54977f96239c
-- title:
--   Is Finite QC: is Finite Presentation
-- statement:
--   The Is Finite QC construction uses the is Finite Presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L413-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L413-L428

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

theorem GlobalTheory.QCoh.IsFiniteQC.isFinitePresentation [IsLocallyNoetherian X] [IsFiniteQC F] :
    F.IsFinitePresentation := by sorry
