-- Prove2me | Theorems.Thm_GlobalTheory_T_mvPolynomial_clear_denominators_eval
-- name    : GlobalTheory.T.mvPolynomial_clear_denominators_eval
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:40.058931+00:00
-- url     : https://prove2.me/theorems/0adf0d16-8e77-45aa-bd12-e838fbe5fe98
-- title:
--   T: mv Polynomial clear denominators eval
-- statement:
--   The T construction uses the mv Polynomial clear denominators eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MvPolynomialClearDenominatorsEvalStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MvPolynomialClearDenominatorsEvalStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEval
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEvalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mvPolynomial_clear_denominators_eval : ∀ {K : Type} [Field K] {ι τ : Type} (F : MvPolynomial ι K) (P D : ι → MvPolynomial τ K), ∃ G M : MvPolynomial τ K, ∀ y : τ → K, (∀ i, MvPolynomial.eval y (D i) ≠ 0) → MvPolynomial.eval y M ≠ 0 ∧ MvPolynomial.eval y G = MvPolynomial.eval y M * MvPolynomial.eval (fun i => MvPolynomial.eval y (P i) / MvPolynomial.eval y (D i)) F := by sorry
