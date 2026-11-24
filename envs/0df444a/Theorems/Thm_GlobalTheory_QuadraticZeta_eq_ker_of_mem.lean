-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_eq_ker_of_mem
-- name    : GlobalTheory.QuadraticZeta.eq_ker_of_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:41.431401+00:00
-- url     : https://prove2.me/theorems/c82e0d77-0c93-480a-837d-3a5f4bbf7561
-- title:
--   Quadratic Zeta: eq ker of mem
-- statement:
--   The Quadratic Zeta construction uses the eq ker of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L203-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L203-L215

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
omit hw

theorem GlobalTheory.QuadraticZeta.eq_ker_of_mem (φ : 𝓞 K →+* ZMod p) {c : ℤ} (hc : φ (b 1) = c) (hm : b 1 - c ∈ P) :
    P = RingHom.ker φ := by sorry
