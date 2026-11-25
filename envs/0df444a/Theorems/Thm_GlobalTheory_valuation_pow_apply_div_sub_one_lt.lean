-- Prove2me | Theorems.Thm_GlobalTheory_valuation_pow_apply_div_sub_one_lt
-- name    : GlobalTheory.valuation_pow_apply_div_sub_one_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:58.954378+00:00
-- url     : https://prove2.me/theorems/6a5fa26c-44bf-46ed-bb97-a0933e5b0137
-- title:
--   Global Theory: valuation pow apply div sub one lt
-- statement:
--   The Global Theory construction uses the valuation pow apply div sub one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ValuationPowApplyDivSubOneLt.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ValuationPowApplyDivSubOneLt.lean#L9-L31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ValuationPowApplyDivSubOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open GlobalTheory
open NumberField IsDedekindDomain

theorem GlobalTheory.valuation_pow_apply_div_sub_one_lt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (x : Ω) (hx : x ≠ 0) (i : ℕ) :
    A.valuation ((σ ^ i) x / x - 1) < 1 := by sorry
