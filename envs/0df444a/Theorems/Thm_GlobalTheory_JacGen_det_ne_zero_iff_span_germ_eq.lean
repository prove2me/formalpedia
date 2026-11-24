-- Prove2me | Theorems.Thm_GlobalTheory_JacGen_det_ne_zero_iff_span_germ_eq
-- name    : GlobalTheory.JacGen.det_ne_zero_iff_span_germ_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:48:50.553148+00:00
-- url     : https://prove2.me/theorems/6e87f4d5-1113-473a-9ea9-6de6033e2d63
-- title:
--   Jac Gen: det ne zero iff span germ eq
-- statement:
--   The Jac Gen construction uses the det ne zero iff span germ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacNeZeroIffSpanEqMaximalIdeal.lean#L194-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/JacNeZeroIffSpanEqMaximalIdeal.lean#L194-L237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacGen
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.LieComb IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))}
variable [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR K ⟶ G)}

theorem GlobalTheory.JacGen.det_ne_zero_iff_span_germ_eq [LocallyOfFiniteType G.hom] (hv : IsLieBasis v) (z : 𝟙_ _ ⟶ G) (p : Sp K)
    {U : G.left.Opens} (hU : z.left p ∈ U) (f : Fin n → Γ(G.left, U))
    (hf : ∀ i, KeyKa.valT (T := K) z.left U (f i) = 0) :
    (Matrix.of fun i k => (KeyKa.valT (T := DualNumber K) ((toUnit (epsR K) ≫ z) * v k).left U (f i)).snd).det ≠ 0 ↔
      Ideal.span (Set.range fun i => (G.left.presheaf.germ U _ hU).hom (f i)) =
        maximalIdeal (G.left.presheaf.stalk (z.left p)) := by sorry
