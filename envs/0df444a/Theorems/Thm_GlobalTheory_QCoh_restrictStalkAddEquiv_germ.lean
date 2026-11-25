-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_restrictStalkAddEquiv_germ
-- name    : GlobalTheory.QCoh.restrictStalkAddEquiv_germ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:02:21.328584+00:00
-- url     : https://prove2.me/theorems/ffc46c92-e752-545d-a7c0-e0e918f2fac4
-- title:
--   QCoh: restrict Stalk Add Equiv germ
-- statement:
--   The QCoh construction uses the restrict Stalk Add Equiv germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L551-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L551-L555

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

theorem GlobalTheory.QCoh.restrictStalkAddEquiv_germ {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (y : Y)
    {W : Y.Opens} (hy : y ∈ W) (s : Γ(F.restrict g, W)) :
    restrictStalkAddEquiv F g y ((F.restrict g).presheaf.germ W y hy s) =
      F.presheaf.germ (g ''ᵁ W) (g y) ⟨y, hy, rfl⟩ ((F.restrictAppIso g W).hom s) := by sorry
