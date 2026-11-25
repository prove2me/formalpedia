-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_restrictStalkAddEquiv_smul
-- name    : GlobalTheory.QCoh.restrictStalkAddEquiv_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:12:03.482041+00:00
-- url     : https://prove2.me/theorems/ddeb59a2-4dbe-417e-a4b4-8e38ca772978
-- title:
--   QCoh: restrict Stalk Add Equiv smul
-- statement:
--   The QCoh construction uses the restrict Stalk Add Equiv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L557-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L557-L579

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

theorem GlobalTheory.QCoh.restrictStalkAddEquiv_smul {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (y : Y)
    (r : X.presheaf.stalk (g y)) (t : ((F.restrict g).presheaf.stalk y :)) :
    restrictStalkAddEquiv F g y (g.stalkMap y r • t) = r • restrictStalkAddEquiv F g y t := by sorry
