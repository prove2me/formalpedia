-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_assPoints_restrict
-- name    : GlobalTheory.QCoh.assPoints_restrict
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:50.094725+00:00
-- url     : https://prove2.me/theorems/e64a0ead-447b-58c1-8329-6b32a2ca72e9
-- title:
--   QCoh: ass Points restrict
-- statement:
--   The QCoh construction uses the ass Points restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L782-L791
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L782-L791

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

theorem GlobalTheory.QCoh.assPoints_restrict {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    assPoints (F.restrict g) = g ⁻¹' assPoints F := by sorry
