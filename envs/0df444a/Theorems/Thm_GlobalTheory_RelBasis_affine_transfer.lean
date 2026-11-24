-- Prove2me | Theorems.Thm_GlobalTheory_RelBasis_affine_transfer
-- name    : GlobalTheory.RelBasis.affine_transfer
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:19:51.240036+00:00
-- url     : https://prove2.me/theorems/dcd6660c-5b02-4f0c-b862-5eb27db26465
-- title:
--   Rel Basis: affine transfer
-- statement:
--   The Rel Basis construction uses the affine transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PullbackSectionsBasisAffineBaseChangeOfAffine.lean#L38-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PullbackSectionsBasisAffineBaseChangeOfAffine.lean#L38-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IndepOnEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PullbackSectionsBasisAffineBaseChangeOfAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.RelBasis
variable {X Y T Y' T' : Scheme.{0}} {L : LB X} {t : ℤ} {N : ℕ}

theorem GlobalTheory.RelBasis.affine_transfer (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X) (W : T.Opens)
    (j : Y' ⟶ Y) (p₁' : Y' ⟶ T') (g : T' ⟶ T) [IsOpenImmersion g] (sq : IsPullback j p₁' p₁ g)
    (hr : Set.range g = W) (e : ⊤ ≤ g ⁻¹ᵁ W) (hb : Function.Bijective (g.appLE W ⊤ e).hom)
    (h₁ : IndepOn b p₁' (j ≫ p₂) ⊤) (h₂ : SpanOn b p₁' (j ≫ p₂) ⊤) :
    IndepOn b p₁ p₂ W ∧ SpanOn b p₁ p₂ W := by sorry
