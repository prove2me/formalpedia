-- Prove2me | Theorems.Thm_GlobalTheory_PowSpan_span_ev
-- name    : GlobalTheory.PowSpan.span_ev
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:29.909073+00:00
-- url     : https://prove2.me/theorems/a41f2c86-ed33-434f-8f43-6482526365d5
-- title:
--   Pow Span: span ev
-- statement:
--   The Pow Span construction uses the span ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/BoxProductsSpanExternalPowersOfBoxSpan.lean#L44-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/BoxProductsSpanExternalPowersOfBoxSpan.lean#L44-L81

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
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxProductsSpanExternalPowersOfBoxSpan
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
open GlobalTheory GlobalTheory.PowSpan
variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

theorem GlobalTheory.PowSpan.span_ev (A : Over (Sp R)) (L : LB A.left) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)) (hL : L.IsLB)
    (hb : ∀ T : Over (Sp R), GlobalTheory.RelBasis.BoxSpan b (snd A T).left (fst A T).left) (n : ℕ) :
    ∀ (s : LB.Sec (LB.LinComb L (K := Fin n) (fun c => (Out.powPr A c).left) (fun _ => t))),
      ∃ q : (Fin n → Fin N) → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ (Out.powObj A n).left) (z : Z) J, Good L z J →
        sval s r z J = ∑ I, ev (r ≫ (Out.powObj A n).hom) z (q I) *
          ∏ c, gs (r ≫ (Out.powPr A c).left) z (L.U (J (r ≫ (Out.powPr A c).left)))
            ((b (I c)).f (J (r ≫ (Out.powPr A c).left))) := by sorry
