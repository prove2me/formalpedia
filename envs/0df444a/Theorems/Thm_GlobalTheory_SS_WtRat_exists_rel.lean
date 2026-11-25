-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_exists_rel
-- name    : GlobalTheory.SS.WtRat.exists_rel
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:33:00.743801+00:00
-- url     : https://prove2.me/theorems/34a9f91f-53a5-405c-9fcf-0444cef87f2e
-- title:
--   Wt Rat: exists rel
-- statement:
--   The Wt Rat construction uses the exists rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRatioOfWeightSums.lean#L71-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRatioOfWeightSums.lean#L71-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightedRelationOfMinimalSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFractionEvalSectionAffineNearPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSums
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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat

theorem GlobalTheory.SS.WtRat.exists_rel {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {X : Type} [AddCommGroup X]
    (i : splitTorus (Sp k) X ⟶ G) {F : Type} [Field F] {s : Sp F ⟶ Sp k} (g : Over.mk s ⟶ G)
    (U : G.left.Opens) (f : Γ(G.left, U)) (h₁ : ⊤ ≤ (((1 : Over.mk s ⟶ splitTorus (Sp k) X) ≫ i) * g).left ⁻¹ᵁ U) :
    ∃ (S : Finset X) (p q : X → F), ∑ χ ∈ S, p χ ≠ 0 ∧
      ∀ (t : Over.mk s ⟶ splitTorus (Sp k) X) (h : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U),
        ev (R := F) ((t ≫ i) * g).left U h f * ∑ χ ∈ S, chr t χ * p χ = ∑ χ ∈ S, chr t χ * q χ := by sorry
