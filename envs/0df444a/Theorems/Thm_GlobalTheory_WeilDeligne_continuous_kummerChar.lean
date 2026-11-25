-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_continuous_kummerChar
-- name    : GlobalTheory.WeilDeligne.continuous_kummerChar
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:02.422629+00:00
-- url     : https://prove2.me/theorems/14d9d01b-a76a-4eb6-aeaa-fa8295cde55d
-- title:
--   Weil Deligne: continuous kummer Char
-- statement:
--   The Weil Deligne construction uses the continuous kummer Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L253-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L253-L255

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
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.WeilDeligne.continuous_kummerChar (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (a : Eˣ) :
    Continuous (kummerChar h hl a) := by sorry
