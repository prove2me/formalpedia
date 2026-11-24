-- Prove2me | Theorems.Thm_GlobalTheory_BoxSection_exists_boxSec
-- name    : GlobalTheory.BoxSection.exists_boxSec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:03:24.838398+00:00
-- url     : https://prove2.me/theorems/d998f8c6-d8b2-4739-8d06-29886a354a8d
-- title:
--   Box Section: exists box Sec
-- statement:
--   The Box Section construction uses the exists box Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean#L89-L94

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

theorem GlobalTheory.BoxSection.exists_boxSec : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : Out.IsPowGrp G' G j) (L : LB G.left) (t : Fin j → L.Sec), L.IsLB → ∃ t' : (Out.boxLB L p.pr).Sec, (∀ (jj : Fin j → L.ι) (h : ∀ i, (Out.boxLB L p.pr).U jj ≤ (p.pr i).left ⁻¹ᵁ L.U (jj i)), t'.f jj = ∏ i, ((p.pr i).left.appLE _ _ (h i)).hom ((t i).f (jj i))) ∧ ∀ s : S, (∀ i, ∃ x : G.left, G.hom x = s ∧ x ∈ Out.nonzeroLocus (t i)) → ∃ y : G'.left, G'.hom y = s ∧ y ∈ Out.nonzeroLocus t' := by sorry
