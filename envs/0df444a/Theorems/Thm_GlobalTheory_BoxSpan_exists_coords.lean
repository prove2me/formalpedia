-- Prove2me | Theorems.Thm_GlobalTheory_BoxSpan_exists_coords
-- name    : GlobalTheory.BoxSpan.exists_coords
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:13.171806+00:00
-- url     : https://prove2.me/theorems/438ee881-ab4f-4897-97ef-cae99e753bf2
-- title:
--   Box Span: exists coords
-- statement:
--   The Box Span construction uses the exists coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/BoxProductsBasisSpanPowObjSections.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/BoxProductsBasisSpanPowObjSections.lean#L57-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_BoxProductsBasisSpanPowObjSections
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
open GlobalTheory GlobalTheory.BoxSpan
variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

theorem GlobalTheory.BoxSpan.exists_coords (x : KeyIn R) {m N : ℕ} (b : Fin N → RR x m) (hb : IsBasis x b)
    (a : LB.Sec (LB.LinComb x.P.L (K := PUnit) (fun _ => 𝟙 x.P.A.left) (fun _ => (m : ℤ)))) :
    ∃ c : Fin N → R, ∀ (Z : Scheme.{0}) (r : Z ⟶ x.P.A.left) (z : Z) J, Good x.P.L z J →
      sval a r z J = ∑ k, ev (r ≫ x.P.A.hom) z (c k) * gs r z (x.P.L.U (J r)) ((b k).f (J r)) := by sorry
