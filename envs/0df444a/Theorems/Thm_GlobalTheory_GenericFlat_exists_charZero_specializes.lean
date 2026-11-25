-- Prove2me | Theorems.Thm_GlobalTheory_GenericFlat_exists_charZero_specializes
-- name    : GlobalTheory.GenericFlat.exists_charZero_specializes
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:19.554425+00:00
-- url     : https://prove2.me/theorems/cb4e7112-2a58-59f1-afca-9244ff5c3cb2
-- title:
--   Generic Flat: exists char Zero specializes
-- statement:
--   The Generic Flat construction uses the exists char Zero specializes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InjectiveOfApplyEqGenericPoint.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InjectiveOfApplyEqGenericPoint.lean#L21-L33

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

theorem GlobalTheory.GenericFlat.exists_charZero_specializes (O : Type) [CommRing O] [IsDomain O] [CharZero O] (T : Scheme.{0})
    (s : T ⟶ Sp O) [Flat s] (x : T) : ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ) := by sorry
