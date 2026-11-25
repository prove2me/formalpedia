-- Prove2me | Theorems.Thm_GlobalTheory_T_coeff_coefficientSpaceAction_mem_range
-- name    : GlobalTheory.T.coeff_coefficientSpaceAction_mem_range
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:29:26.585673+00:00
-- url     : https://prove2.me/theorems/cab5bfa7-1d7a-4696-bc1e-5075efa044b6
-- title:
--   T: coeff coefficient Space Action mem range
-- statement:
--   The T construction uses the coeff coefficient Space Action mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffCoefficientSpaceActionMemRangeStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CoeffCoefficientSpaceActionMemRangeStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffCoefficientSpaceActionMemRange
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ReprMemOfCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CoeffCoefficientSpaceActionMemRangeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.coeff_coefficientSpaceAction_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, MvPolynomial.coeff m v.1 ∈ Set.range κ) → ∀ m, MvPolynomial.coeff m ((rhoVr emb lam g) v).1 ∈ Set.range κ := by sorry
