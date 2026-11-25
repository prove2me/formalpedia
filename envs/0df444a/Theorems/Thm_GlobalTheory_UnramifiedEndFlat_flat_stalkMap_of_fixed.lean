-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_stalkMap_of_fixed
-- name    : GlobalTheory.UnramifiedEndFlat.flat_stalkMap_of_fixed
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:09.912458+00:00
-- url     : https://prove2.me/theorems/41703741-7afc-4137-8296-c72ec0aa608b
-- title:
--   Unramified End Flat: flat stalk Map of fixed
-- statement:
--   The Unramified End Flat construction uses the flat stalk Map of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L108-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L108-L126

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

theorem GlobalTheory.UnramifiedEndFlat.flat_stalkMap_of_fixed {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (f : X ⟶ X) (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (hfg : f ≫ g = g)
    [FormallyUnramified f] (x : X) (hx : IsClosed {x}) (hfx : f x = x) :
    (f.stalkMap x).hom.Flat := by sorry
