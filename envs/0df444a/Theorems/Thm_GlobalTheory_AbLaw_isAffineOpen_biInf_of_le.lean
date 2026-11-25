-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_isAffineOpen_biInf_of_le
-- name    : GlobalTheory.AbLaw.isAffineOpen_biInf_of_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:07:56.433245+00:00
-- url     : https://prove2.me/theorems/0ec78443-4d78-50ad-a3b9-61f268e01b43
-- title:
--   Ab Law: is Affine Open bi Inf of le
-- statement:
--   The Ab Law construction uses the is Affine Open bi Inf of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineOpenBiInfOfLe.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineOpenBiInfOfLe.lean#L21-L31

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

theorem GlobalTheory.AbLaw.isAffineOpen_biInf_of_le (E : ν → Y.Opens)
    (hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V)) (u : Finset ν) {V : Y.Opens}
    (hV : IsAffineOpen V) (h : ⨅ i ∈ u, E i ≤ V) : IsAffineOpen (⨅ i ∈ u, E i) := by sorry
