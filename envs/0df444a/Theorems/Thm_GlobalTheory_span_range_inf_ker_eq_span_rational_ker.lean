-- Prove2me | Theorems.Thm_GlobalTheory_span_range_inf_ker_eq_span_rational_ker
-- name    : GlobalTheory.span_range_inf_ker_eq_span_rational_ker
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:50.51681+00:00
-- url     : https://prove2.me/theorems/c57a17b0-d7da-46e8-be58-2c44ce74925e
-- title:
--   Global Theory: span range inf ker eq span rational ker
-- statement:
--   The Global Theory construction uses the span range inf ker eq span rational ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanRangeInfKerEqSpanRationalKer.lean#L17-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanRangeInfKerEqSpanRationalKer.lean#L17-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanRangeInfKerEqSpanRationalKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.span_range_inf_ker_eq_span_rational_ker {K : Type} [Field K] (σ : K →+* ℂ) {W E : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] {n d : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : (Fin d → K) →ₛₗ[σ] E) (f : W →ₗ[ℂ] E)
    (M : Matrix (Fin d) (Fin n) K)
    (hli : LinearIndependent ℂ (fun l => j' (Pi.single l 1)))
    (hf : ∀ x, f (j x) = j' (M.mulVec x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f
      = Submodule.span ℂ (j '' {x | M.mulVec x = 0}) := by sorry
