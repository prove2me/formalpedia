-- Prove2me | Theorems.Thm_GlobalTheory_BoxSection_mem_basicOpen_prod
-- name    : GlobalTheory.BoxSection.mem_basicOpen_prod
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:04:16.902887+00:00
-- url     : https://prove2.me/theorems/43d3971b-dcec-4e25-86dd-bcb056b7b72f
-- title:
--   Box Section: mem basic Open prod
-- statement:
--   The Box Section construction uses the mem basic Open prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusProdSec.lean#L50-L53

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

theorem GlobalTheory.BoxSection.mem_basicOpen_prod {Y : Scheme.{0}} {K : Type} [Fintype K] {W : Y.Opens} (a : K → Γ(Y, W))
    {y : Y} (hy : y ∈ W) (h : ∀ i, y ∈ Y.basicOpen (a i)) : y ∈ Y.basicOpen (∏ i, a i) := by sorry
