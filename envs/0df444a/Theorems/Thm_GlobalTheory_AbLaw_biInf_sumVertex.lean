-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_biInf_sumVertex
-- name    : GlobalTheory.AbLaw.biInf_sumVertex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:09:57.856211+00:00
-- url     : https://prove2.me/theorems/424c457a-e627-5dce-9ed9-c540a2adbb80
-- title:
--   Ab Law: bi Inf sum Vertex
-- statement:
--   The Ab Law construction uses the bi Inf sum Vertex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineOpenBiInfOfLe.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineOpenBiInfOfLe.lean#L54-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineOpenBiInfOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
  {ν κ : Type}

theorem GlobalTheory.AbLaw.biInf_sumVertex [LinearOrder ν] [LinearOrder κ] (E : ν ⊕ₗ κ → Y.Opens) (s : Finset ν)
    (t : Finset κ) : ⨅ i ∈ Cube.sumVertex s t, E i =
      (⨅ i ∈ s, E (toLex (Sum.inl i))) ⊓ ⨅ k ∈ t, E (toLex (Sum.inr k)) := by sorry
