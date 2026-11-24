-- Prove2me | Theorems.Thm_GlobalTheory_QFam_sum_eval_eq_of_sum_monomial_eq
-- name    : GlobalTheory.QFam.sum_eval_eq_of_sum_monomial_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:59:28.643503+00:00
-- url     : https://prove2.me/theorems/e9017170-b5bd-40d1-b4f9-06be912b7e44
-- title:
--   QFam: sum eval eq of sum monomial eq
-- statement:
--   The QFam construction uses the sum eval eq of sum monomial eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPermOfSumMonomialEq.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPermOfSumMonomialEq.lean#L9-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMvPolynomialPickPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPermOfSumMonomialEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.sum_eval_eq_of_sum_monomial_eq {ι S : Type} [Fintype ι] [Fintype S] (x y : ι → S → ℂ)
    (h : ∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) (Q : MvPolynomial S ℂ) :
    ∑ i, MvPolynomial.eval (x i) Q = ∑ i, MvPolynomial.eval (y i) Q := by sorry
