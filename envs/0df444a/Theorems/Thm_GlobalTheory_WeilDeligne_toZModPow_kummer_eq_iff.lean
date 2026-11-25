-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_toZModPow_kummer_eq_iff
-- name    : GlobalTheory.WeilDeligne.toZModPow_kummer_eq_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:04:42.136583+00:00
-- url     : https://prove2.me/theorems/fd52c877-4abc-4869-8ae6-2c4ba585e247
-- title:
--   Weil Deligne: to ZMod Pow kummer eq iff
-- statement:
--   The Weil Deligne construction uses the to ZMod Pow kummer eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L181-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L181-L187

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
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable (l : ℕ) [Fact l.Prime]

theorem GlobalTheory.WeilDeligne.toZModPow_kummer_eq_iff (a : Eˣ) (σ τ : G E Ω) (n : ℕ) :
    PadicInt.toZModPow n (kummer l a σ) = PadicInt.toZModPow n (kummer l a τ) ↔
      σ (rootOf Ω l (a : E) n) = τ (rootOf Ω l (a : E) n) := by sorry
