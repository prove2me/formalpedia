-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_rem_eq
-- name    : GlobalTheory.CharFormDeriv.rem_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:27.342403+00:00
-- url     : https://prove2.me/theorems/09ab0a22-fe01-4725-8362-3a15e0c26034
-- title:
--   Char Form Deriv: rem eq
-- statement:
--   The Char Form Deriv construction uses the rem eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L66-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L66-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv

theorem GlobalTheory.CharFormDeriv.rem_eq {t : ℝ} (ht0 : t ≠ 0) (y : ℝ) :
    rem t y = (t : ℂ)⁻¹ * (Complex.exp (((t * y : ℝ) : ℂ) * I) - 1 - ((t * y : ℝ) : ℂ) * I) := by sorry
