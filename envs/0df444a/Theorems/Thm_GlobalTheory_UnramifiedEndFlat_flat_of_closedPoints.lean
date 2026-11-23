-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_of_closedPoints
-- name    : GlobalTheory.UnramifiedEndFlat.flat_of_closedPoints
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:41.794144+00:00
-- url     : https://prove2.me/theorems/2379bfb5-8d05-45d2-9c9a-38a4ae07ae87
-- title:
--   Unramified End Flat: flat of closed Points
-- statement:
--   The Unramified End Flat construction uses the flat of closed Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L89-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
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
open GlobalTheory.UnramifiedEndFlat
open IsLocalRing

theorem GlobalTheory.UnramifiedEndFlat.flat_of_closedPoints {X Y : Scheme.{0}} [JacobsonSpace X] (f : X ⟶ Y)
    (hf : ∀ x : X, IsClosed {x} → (f.stalkMap x).hom.Flat) : Flat f := by sorry
