-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_numeric
-- name    : GlobalTheory.RegBound.numeric
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:57.694104+00:00
-- url     : https://prove2.me/theorems/5564fb79-d08f-4e45-afda-b0213cea8def
-- title:
--   Reg Bound: numeric
-- statement:
--   The Reg Bound construction uses the numeric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L251-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L251-L296

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]

theorem GlobalTheory.RegBound.numeric {g : ℕ → ℚ} {δ : ℕ → ℕ} {d B : ℕ} (h1 : ∀ e ≥ d, g (e + 1) = g e - δ (e + 1))
    (h2 : ∀ᶠ e in atTop, g e = 0) (h3 : g d ≤ B) (h4 : ∀ e ≥ d, δ e = 0 → δ (e + 1) = 0) :
    ∀ e ≥ d + B + 1, δ e = 0 ∧ g e = 0 := by sorry
