-- Prove2me | Theorems.Thm_GlobalTheory_SS_Ord_exists_j_eq_of_rs
-- name    : GlobalTheory.SS.Ord.exists_j_eq_of_rs
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:17:32.799321+00:00
-- url     : https://prove2.me/theorems/5b349214-c3b5-494a-9c76-19da39c9d3e7
-- title:
--   Ord: exists j eq of rs
-- statement:
--   The Ord construction uses the exists j eq of rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L356-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L356-L368

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
  [IsFractionRing R K] {A : Over (Sp K)} {π : R}

theorem GlobalTheory.SS.Ord.exists_j_eq_of_rs (hπ : Irreducible π) (M : Model R A) (hM : M.Irr) {U W : M.Y.left.Opens}
    (hU : IsAffineOpen U) (hW : W ≤ U) (h : ((W : Set M.Y.left) ∩ M.sp).Nonempty)
    (f : Γ(A.left, M.j ⁻¹ᵁ U)) (s : Γ(M.Y.left, W)) (hs : (M.j.app W).hom s = rs _ (M.j.preimage_mono hW) f) :
    ∃ b, (M.j.app U).hom b = f := by sorry
