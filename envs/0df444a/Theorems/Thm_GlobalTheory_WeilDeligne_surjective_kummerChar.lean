-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_surjective_kummerChar
-- name    : GlobalTheory.WeilDeligne.surjective_kummerChar
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:04:42.547113+00:00
-- url     : https://prove2.me/theorems/d65c5ada-a948-4387-b24d-ee33ab2ec2d3
-- title:
--   Weil Deligne: surjective kummer Char
-- statement:
--   The Weil Deligne construction uses the surjective kummer Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L303-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ToZModPowKummerEqIff.lean#L303-L312

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

theorem GlobalTheory.WeilDeligne.surjective_kummerChar (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (a : Eˣ)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (hx : σ (rootOf Ω l (a : E) 1) ≠ rootOf Ω l (a : E) 1) :
    Function.Surjective (kummerChar h hl a) := by sorry
