-- Prove2me | Theorems.Thm_GlobalTheory_GenericFlat_generic_charZero_and_flat
-- name    : GlobalTheory.GenericFlat.generic_charZero_and_flat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:05:44.295791+00:00
-- url     : https://prove2.me/theorems/70e75efa-33dd-5b65-b740-78c5dfbf169b
-- title:
--   Generic Flat: generic char Zero and flat
-- statement:
--   The Generic Flat construction uses the generic char Zero and flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InjectiveOfApplyEqGenericPoint.lean#L51-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/InjectiveOfApplyEqGenericPoint.lean#L51-L94

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

theorem GlobalTheory.GenericFlat.generic_charZero_and_flat : (∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Flat s → ∀ x : T, ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ)) ∧ ∀ (R O : Type) [CommRing R] [IsDedekindDomain R] [CommRing O] [IsDomain O] (b : R →+* O) (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ T) (v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Function.Injective b → Flat s → Set.range x ⊆ genericPoints T → x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap V K) ≫ v → Flat (v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b) := by sorry
