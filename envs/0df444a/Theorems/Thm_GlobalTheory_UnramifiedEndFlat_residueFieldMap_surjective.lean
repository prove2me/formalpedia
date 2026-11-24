-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedEndFlat_residueFieldMap_surjective
-- name    : GlobalTheory.UnramifiedEndFlat.residueFieldMap_surjective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:47.45265+00:00
-- url     : https://prove2.me/theorems/a07e7493-a971-41da-8b22-758acb24cb12
-- title:
--   Unramified End Flat: residue Field Map surjective
-- statement:
--   The Unramified End Flat construction uses the residue Field Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L96-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFormallyUnramifiedGrpEnd.lean#L96-L106

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

theorem GlobalTheory.UnramifiedEndFlat.residueFieldMap_surjective {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ g)] (x : X)
    (hx : IsClosed {x}) : Function.Surjective (f.residueFieldMap x) := by sorry
