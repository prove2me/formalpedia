-- Prove2me | Theorems.Thm_GlobalTheory_FibreFlat_FlatOver_target
-- name    : GlobalTheory.FibreFlat.FlatOver.target
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:36.155278+00:00
-- url     : https://prove2.me/theorems/f99d6dbc-714d-43a9-842f-8098877ef4cc
-- title:
--   Flat Over: target
-- statement:
--   The Flat Over construction uses the target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FlatOfFlatFibresDvr.lean#L86-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
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
open TensorProduct IsLocalRing
open GlobalTheory
open GlobalTheory.FibreFlat
variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ S} {s : S' ⟶ S}

theorem GlobalTheory.FibreFlat.FlatOver.target (H : FlatOver f g s) {X' Y' : Scheme.{0}} {a' : X' ⟶ X} {f' : X' ⟶ Y'}
    {u : Y' ⟶ Y} (sq : IsPullback a' f' f u) : FlatOver f' (u ≫ g) s := by sorry
