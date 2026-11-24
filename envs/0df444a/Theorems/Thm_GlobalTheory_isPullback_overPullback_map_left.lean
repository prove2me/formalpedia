-- Prove2me | Theorems.Thm_GlobalTheory_isPullback_overPullback_map_left
-- name    : GlobalTheory.isPullback_overPullback_map_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:59:32.348794+00:00
-- url     : https://prove2.me/theorems/e2b7c187-2780-422c-b522-a0bdb81d5d5c
-- title:
--   Global Theory: is Pullback over Pullback map left
-- statement:
--   The Global Theory construction uses the is Pullback over Pullback map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/RingHomFlatCodescendsAlongFaithfullyFlat.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/RingHomFlatCodescendsAlongFaithfullyFlat.lean#L22-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.isPullback_overPullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S}
    (φ : X ⟶ Y) :
    IsPullback ((Over.pullback f).map φ).left (pullback.fst X.hom f) (pullback.fst Y.hom f)
      φ.left := by sorry
