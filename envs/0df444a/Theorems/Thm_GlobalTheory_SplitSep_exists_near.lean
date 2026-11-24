-- Prove2me | Theorems.Thm_GlobalTheory_SplitSep_exists_near
-- name    : GlobalTheory.SplitSep.exists_near
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:41.197695+00:00
-- url     : https://prove2.me/theorems/f5ea1cb5-8caf-4f56-a55c-6f0500d8bcae
-- title:
--   Split Sep: exists near
-- statement:
--   The Split Sep construction uses the exists near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsIntegerUnitSplitPlaceConjugatePrime.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsIntegerUnitSplitPlaceConjugatePrime.lean#L16-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_Automorphisms_Unitary
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
noncomputable section
open GlobalTheory GlobalTheory.SplitSep
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
local notation3 "cc" => IsCMField.complexConj L

theorem GlobalTheory.SplitSep.exists_near (v : HeightOneSpectrum (𝓞 L⁺))
    (f : v.adicCompletion L⁺ → v.adicCompletion L⁺) (hf : Continuous f)
    (y₀ : v.adicCompletion L⁺) (hy₀ : Valued.v (f y₀) < 1) :
    ∃ a : L⁺, Valued.v (f (algebraMap L⁺ (v.adicCompletion L⁺) a)) < 1 := by sorry
