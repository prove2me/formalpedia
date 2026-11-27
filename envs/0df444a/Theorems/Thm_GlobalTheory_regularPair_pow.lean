-- Prove2me | Theorems.Thm_GlobalTheory_regularPair_pow
-- name    : GlobalTheory.regularPair_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:50:10.76143+00:00
-- url     : https://prove2.me/theorems/af8cc89b-5bf0-4273-9676-21d5d23040df
-- title:
--   Global Theory: regular Pair pow
-- statement:
--   The Global Theory construction uses the regular Pair pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivMemOfMulPowDivMemOfRegularPair.lean#L16-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivMemOfMulPowDivMemOfRegularPair.lean#L16-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivMemOfMulPowDivMemOfRegularPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.regularPair_pow : ∀ (K : Type) [Field K] (O : Subring K) (s t : K), s ∈ O → t ∈ O → s ≠ 0 → (∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) → ∀ (m N : ℕ), ∀ g ∈ O, g * t ^ N / s ^ m ∈ O → g / s ^ m ∈ O := by sorry
