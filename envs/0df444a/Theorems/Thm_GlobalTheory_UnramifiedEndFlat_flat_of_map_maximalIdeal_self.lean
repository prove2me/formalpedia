-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_of_map_maximalIdeal_self
-- name    : GlobalTheory.UnramifiedEndFlat.flat_of_map_maximalIdeal_self
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:46.221109+00:00
-- url     : https://prove2.me/theorems/b8277fcf-53d6-4e09-b9f0-d432691f3300
-- title:
--   Unramified End Flat: flat of map maximal Ideal self
-- statement:
--   The Unramified End Flat construction uses the flat of map maximal Ideal self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L15-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L15-L40

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

theorem GlobalTheory.UnramifiedEndFlat.flat_of_map_maximalIdeal_self {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (φ : A →+* A) (hm : (maximalIdeal A).map φ = maximalIdeal A)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal A) : φ.Flat := by sorry
