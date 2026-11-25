-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_kummerChar_ineConj
-- name    : GlobalTheory.WeilDeligne.kummerChar_ineConj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:04:17.135616+00:00
-- url     : https://prove2.me/theorems/f315f030-94f1-4372-9646-e29db8108920
-- title:
--   Weil Deligne: kummer Char ine Conj
-- statement:
--   The Weil Deligne construction uses the kummer Char ine Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L257-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L257-L266

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

theorem GlobalTheory.WeilDeligne.kummerChar_ineConj {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (a : Eˣ)
    (g : Weil h) (σ : Ine (F := E) A) :
    ((kummerChar h hl a (ineConj g σ)).toAdd : ℚ_[l]) =
      ((normV w : ℕ) : ℚ_[l]) ^ deg g * ((kummerChar h hl a σ).toAdd : ℚ_[l]) := by sorry
