-- Prove2me | Theorems.Thm_GlobalTheory_SS_Ord_forall_of_affine
-- name    : GlobalTheory.SS.Ord.forall_of_affine
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:17:14.863087+00:00
-- url     : https://prove2.me/theorems/e195d688-3f61-46f9-b980-80b74b7c493d
-- title:
--   Ord: forall of affine
-- statement:
--   The Ord construction uses the forall of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L470-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L470-L514

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Ord
variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] {A : Over (Sp K)} {π : R} {I : Type} [Fintype I] [DecidableEq I]

theorem GlobalTheory.SS.Ord.forall_of_affine (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) (D : I → VF A)
    {U₀ : M.Y.left.Opens} (hU₀ : IsAffineOpen U₀) (h₀ : ((U₀ : Set M.Y.left) ∩ M.sp).Nonempty) {n : ℤ}
    (hn : ∀ t : I → Γ(M.Y.left, U₀), ∃ s : Γ(M.Y.left, U₀),
      jac D (M.j ⁻¹ᵁ U₀) (fun i => (M.j.app U₀).hom (t i)) =
        cstK A _ (algebraMap R K π ^ n) * (M.j.app U₀).hom s)
    (U : M.Y.left.Opens) (t : I → Γ(M.Y.left, U)) : ∃ s : Γ(M.Y.left, U),
      jac D (M.j ⁻¹ᵁ U) (fun i => (M.j.app U).hom (t i)) =
        cstK A _ (algebraMap R K π ^ n) * (M.j.app U).hom s := by sorry
