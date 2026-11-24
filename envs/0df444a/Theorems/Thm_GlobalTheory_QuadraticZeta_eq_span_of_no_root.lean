-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_eq_span_of_no_root
-- name    : GlobalTheory.QuadraticZeta.eq_span_of_no_root
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:33.722232+00:00
-- url     : https://prove2.me/theorems/5b4d2e1c-4adb-480c-894a-f539bccf100a
-- title:
--   Quadratic Zeta: eq span of no root
-- statement:
--   The Quadratic Zeta construction uses the eq span of no root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L177-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L177-L200

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]
variable (b : Basis (Fin 2) ℤ (𝓞 K)) (h0 : b 0 = 1) {t n : ℤ} (hw : b 1 ^ 2 = t * b 1 - n)
  {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hPm : P.IsMaximal)
  (hP : P.under ℤ = .span {(p : ℤ)})
include h0 hw hp hPm hP

theorem GlobalTheory.QuadraticZeta.eq_span_of_no_root (h : ∀ β : ZMod p, β ^ 2 ≠ t * β - n) :
    P = Ideal.span {(p : 𝓞 K)} := by sorry
