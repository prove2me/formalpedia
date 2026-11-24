-- Prove2me | Theorems.Thm_GlobalTheory_extend_alg_hom_adjoin_integral_root
-- name    : GlobalTheory.extend_alg_hom_adjoin_integral_root
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:16.541789+00:00
-- url     : https://prove2.me/theorems/561f5401-2233-4853-924a-25982036d295
-- title:
--   Global Theory: extend alg hom adjoin integral root
-- statement:
--   The Global Theory construction uses the extend alg hom adjoin integral root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAlgHomAdjoinIntegralRoot.lean#L7-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAlgHomAdjoinIntegralRoot.lean#L7-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAlgHomAdjoinIntegralRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial

theorem GlobalTheory.extend_alg_hom_adjoin_integral_root :
    ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω]
    (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ →
    ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 →
    ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω,
      ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))),
        ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by sorry
