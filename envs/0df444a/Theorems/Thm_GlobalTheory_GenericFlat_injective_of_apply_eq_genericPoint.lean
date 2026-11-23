-- Prove2me | Theorems.Thm_GlobalTheory_GenericFlat_injective_of_apply_eq_genericPoint
-- name    : GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:28.076831+00:00
-- url     : https://prove2.me/theorems/56c66282-3914-4f65-871a-842fbe8efa38
-- title:
--   Generic Flat: injective of apply eq generic Point
-- statement:
--   The Generic Flat construction uses the injective of apply eq generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InjectiveOfApplyEqGenericPoint.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InjectiveOfApplyEqGenericPoint.lean#L10-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InjectiveOfApplyEqGenericPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GenericFlat
open AlgebraicGeometry CategoryTheory Limits

theorem GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint {O K : Type} [CommRing O] [IsDomain O] [Field K]
    (δ : O →+* K) (pt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap δ pt = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)) :
    Function.Injective δ := by sorry
