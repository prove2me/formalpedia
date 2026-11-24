-- Prove2me | Theorems.Thm_GlobalTheory_BoxSection_exists_point_powObj
-- name    : GlobalTheory.BoxSection.exists_point_powObj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:03:15.134519+00:00
-- url     : https://prove2.me/theorems/42aedde6-eec1-4f1b-b613-e76b0eaefac2
-- title:
--   Box Section: exists point pow Obj
-- statement:
--   The Box Section construction uses the exists point pow Obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean#L63-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean#L63-L77

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

theorem GlobalTheory.BoxSection.exists_point_powObj {S : Scheme.{0}} (G : Over S) (s : S) :
    ∀ (n : ℕ) (x : Fin n → G.left), (∀ i, G.hom (x i) = s) →
      ∃ y : (Out.powObj G n).left, (Out.powObj G n).hom y = s ∧
        ∀ i, (Out.powPr G i).left y = x i
  := by sorry
