-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_acyclic_comap_secCube
-- name    : GlobalTheory.AbLaw.acyclic_comap_secCube
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:07:51.662065+00:00
-- url     : https://prove2.me/theorems/d11ee013-759c-5a1d-a5d3-5607a1278b77
-- title:
--   Ab Law: acyclic comap sec Cube
-- statement:
--   The Ab Law construction uses the acyclic comap sec Cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineOpenBiInfOfLe.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineOpenBiInfOfLe.lean#L33-L42

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

theorem GlobalTheory.AbLaw.acyclic_comap_secCube [LinearOrder ν] [LinearOrder κ] [Fintype κ] (hM : M.IsLB)
    (E : ν → Y.Opens) (hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V)) (e : κ ↪o ν)
    (hc : ⨆ k, E (e k) = ⊤) (s₀ : Finset ν) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : ⨅ i ∈ s₀, E i ≤ V) (g : Finset κ → Finset ν) (hg : Monotone g)
    (hgs : ∀ t, g t = s₀ ∪ t.map e.toEmbedding) :
    (cubeComplex (Cube.comap g hg (secCube f M E))).Acyclic := by sorry
