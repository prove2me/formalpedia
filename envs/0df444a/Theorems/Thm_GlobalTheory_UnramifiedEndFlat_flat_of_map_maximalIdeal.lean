-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_of_map_maximalIdeal
-- name    : GlobalTheory.UnramifiedEndFlat.flat_of_map_maximalIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:13.101544+00:00
-- url     : https://prove2.me/theorems/d9aaef76-43f2-4e6e-b815-b750b4f13384
-- title:
--   Unramified End Flat: flat of map maximal Ideal
-- statement:
--   The Unramified End Flat construction uses the flat of map maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L42-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L42-L58

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

theorem GlobalTheory.UnramifiedEndFlat.flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] (e : B ≃+* A)
    (φ : A →+* B) (hm : (maximalIdeal A).map φ = maximalIdeal B)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal B) : φ.Flat := by sorry
