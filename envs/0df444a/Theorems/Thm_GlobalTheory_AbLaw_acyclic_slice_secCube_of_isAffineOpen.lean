-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_acyclic_slice_secCube_of_isAffineOpen
-- name    : GlobalTheory.AbLaw.acyclic_slice_secCube_of_isAffineOpen
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:32.159852+00:00
-- url     : https://prove2.me/theorems/e11480a5-601c-4834-b429-56b437873c62
-- title:
--   Ab Law: acyclic slice sec Cube of is Affine Open
-- statement:
--   The Ab Law construction uses the acyclic slice sec Cube of is Affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AcyclicSliceSecCubeOfIsAffineOpen.lean#L96-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AcyclicSliceSecCubeOfIsAffineOpen.lean#L96-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {Y : Scheme.{0}} (M : LB Y)
variable {M}

theorem GlobalTheory.AbLaw.acyclic_slice_secCube_of_isAffineOpen :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (μ κ : Type) [LinearOrder μ] [LinearOrder κ] [Fintype κ] (D : μ → Y.Opens) (e : κ ↪o μ) (s₀ : Finset μ), M.IsLB → (⨅ i ∈ s₀, D i) ≤ ⨆ k, D (e k) → (∀ t : Finset κ, IsAffineOpen (⨅ i ∈ s₀ ∪ t.map e.toEmbedding, D i)) → (cubeComplex (Cube.slice e s₀ (secCube f M D))).Acyclic := by sorry
