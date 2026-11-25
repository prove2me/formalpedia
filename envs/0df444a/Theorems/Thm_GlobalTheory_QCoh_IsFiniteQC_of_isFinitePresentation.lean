-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_IsFiniteQC_of_isFinitePresentation
-- name    : GlobalTheory.QCoh.IsFiniteQC.of_isFinitePresentation
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:16:37.916547+00:00
-- url     : https://prove2.me/theorems/d1a1bdac-3406-45c1-87eb-1022d2ee0a0d
-- title:
--   Is Finite QC: of is Finite Presentation
-- statement:
--   The Is Finite QC construction uses the of is Finite Presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L408-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L408-L409

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

theorem GlobalTheory.QCoh.IsFiniteQC.of_isFinitePresentation [F.IsFinitePresentation] : IsFiniteQC F := by sorry
