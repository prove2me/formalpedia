-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_cycZ_weil
-- name    : GlobalTheory.WeilDeligne.cycZ_weil
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:04:41.065667+00:00
-- url     : https://prove2.me/theorems/f05fb3e8-37e7-43d8-b27e-e150d09d331e
-- title:
--   Weil Deligne: cyc Z weil
-- statement:
--   The Weil Deligne construction uses the cyc Z weil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L209-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L209-L225

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

theorem GlobalTheory.WeilDeligne.cycZ_weil {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (g : Weil h) :
    (((cycZ E Ω l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = ((normV w : ℕ) : ℚ_[l]) ^ deg g := by sorry
