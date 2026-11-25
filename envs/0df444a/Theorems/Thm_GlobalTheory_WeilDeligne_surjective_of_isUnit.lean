-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_surjective_of_isUnit
-- name    : GlobalTheory.WeilDeligne.surjective_of_isUnit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:05:04.034944+00:00
-- url     : https://prove2.me/theorems/5b06c52b-5266-4a00-a634-397fadb732f3
-- title:
--   Weil Deligne: surjective of is Unit
-- statement:
--   The Weil Deligne construction uses the surjective of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L290-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L290-L301

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

theorem GlobalTheory.WeilDeligne.surjective_of_isUnit {H : Type*} [Group H] [TopologicalSpace H] [CompactSpace H]
    {t : H →* Multiplicative ℤ_[l]} (ht : Continuous t) {σ : H} (hσ : IsUnit (t σ).toAdd) :
    Function.Surjective t := by sorry
