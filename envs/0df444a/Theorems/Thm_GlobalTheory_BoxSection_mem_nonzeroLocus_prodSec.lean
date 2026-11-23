-- Prove2me | Theorems.Thm_GlobalTheory_BoxSection_mem_nonzeroLocus_prodSec
-- name    : GlobalTheory.BoxSection.mem_nonzeroLocus_prodSec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:40.923628+00:00
-- url     : https://prove2.me/theorems/c29bd3b7-f210-47fe-8d7f-adb4e1c21876
-- title:
--   Box Section: mem nonzero Locus prod Sec
-- statement:
--   The Box Section construction uses the mem nonzero Locus prod Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean#L55-L61

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

theorem GlobalTheory.BoxSection.mem_nonzeroLocus_prodSec {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (t : K → L.Sec) (y : Y) (h : ∀ i, φ i y ∈ Out.nonzeroLocus (t i)) :
    y ∈ Out.nonzeroLocus (prodSec L φ t) := by sorry
