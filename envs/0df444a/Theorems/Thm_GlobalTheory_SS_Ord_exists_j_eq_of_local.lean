-- Prove2me | Theorems.Thm_GlobalTheory_SS_Ord_exists_j_eq_of_local
-- name    : GlobalTheory.SS.Ord.exists_j_eq_of_local
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:17:12.710906+00:00
-- url     : https://prove2.me/theorems/16c1c522-c878-43db-b6c4-e37f16c07159
-- title:
--   Ord: exists j eq of local
-- statement:
--   The Ord construction uses the exists j eq of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L225-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueModelHasJacobianOrder.lean#L225-L240

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
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

theorem GlobalTheory.SS.Ord.exists_j_eq_of_local [IsDomain R] [IsFractionRing R K] (M : Model R A) (U : M.Y.left.Opens)
    (f : Γ(A.left, M.j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (W : M.Y.left.Opens) (hW : W ≤ U), x ∈ W ∧
      ∃ s, (M.j.app W).hom s = rs _ (M.j.preimage_mono hW) f) : ∃ s, (M.j.app U).hom s = f := by sorry
