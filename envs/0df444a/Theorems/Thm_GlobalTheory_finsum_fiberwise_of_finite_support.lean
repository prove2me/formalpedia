-- Prove2me | Theorems.Thm_GlobalTheory_finsum_fiberwise_of_finite_support
-- name    : GlobalTheory.finsum_fiberwise_of_finite_support
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:50:53.837744+00:00
-- url     : https://prove2.me/theorems/f788b499-7f73-456e-a0a8-3a169563b0f3
-- title:
--   Global Theory: finsum fiberwise of finite support
-- statement:
--   The Global Theory construction uses the finsum fiberwise of finite support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumFiberwiseOfFiniteSupportComplex.lean#L5-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumFiberwiseOfFiniteSupportComplex.lean#L5-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumFiberwiseOfFiniteSupportComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finsum_fiberwise_of_finite_support {A B : Type} (ρ : A → B) (f : A → ℂ)
    (hf : (Function.support f).Finite) :
    ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // ρ a = b}, f a.1 := by sorry
