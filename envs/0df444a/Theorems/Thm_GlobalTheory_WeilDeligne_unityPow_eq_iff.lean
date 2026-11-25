-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_unityPow_eq_iff
-- name    : GlobalTheory.WeilDeligne.unityPow_eq_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:03:39.931025+00:00
-- url     : https://prove2.me/theorems/46f0759a-37f2-5d62-ae1c-097274e02434
-- title:
--   Weil Deligne: unity Pow eq iff
-- statement:
--   The Weil Deligne construction uses the unity Pow eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L70-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime]
variable (Ω) [CharZero Ω]

theorem GlobalTheory.WeilDeligne.unityPow_eq_iff {n : ℕ} {c d : ℤ_[l]} :
    unityPow Ω l n c = unityPow Ω l n d ↔ PadicInt.toZModPow n c = PadicInt.toZModPow n d := by sorry
