-- Prove2me | Theorems.Thm_GlobalTheory_clearDenominators
-- name    : GlobalTheory.clearDenominators
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:43.728383+00:00
-- url     : https://prove2.me/theorems/a6842a4f-f7b5-4c1d-9e1a-f9313428c274
-- title:
--   Global Theory: clear Denominators
-- statement:
--   The Global Theory construction uses the clear Denominators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MvPolynomialClearDenominatorsEval.lean#L7-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MvPolynomialClearDenominatorsEval.lean#L7-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial Finset

theorem GlobalTheory.clearDenominators {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K)
    (P D : ι → MvPolynomial τ K) :
    ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) →
      MvPolynomial.eval y M ≠ 0 ∧
      MvPolynomial.eval y G = MvPolynomial.eval y M *
        MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by sorry
