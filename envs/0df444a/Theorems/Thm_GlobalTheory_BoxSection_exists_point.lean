-- Prove2me | Theorems.Thm_GlobalTheory_BoxSection_exists_point
-- name    : GlobalTheory.BoxSection.exists_point
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:03:40.377233+00:00
-- url     : https://prove2.me/theorems/cab1868b-73b7-4a3f-afef-fa3fa5191d99
-- title:
--   Box Section: exists point
-- statement:
--   The Box Section construction uses the exists point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean#L79-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusProdSec
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
open GlobalTheory GlobalTheory.BoxSection

theorem GlobalTheory.BoxSection.exists_point {S : Scheme.{0}} {G' G : Over S} {n : ℕ} (pr : Fin n → (G' ⟶ G))
    (lim : IsLimit (Fan.mk G' pr)) (s : S) (x : Fin n → G.left) (hx : ∀ i, G.hom (x i) = s) :
    ∃ y : G'.left, G'.hom y = s ∧ ∀ i, (pr i).left y = x i := by sorry
