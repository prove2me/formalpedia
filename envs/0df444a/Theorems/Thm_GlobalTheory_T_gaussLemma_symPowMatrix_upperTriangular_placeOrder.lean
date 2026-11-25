-- Prove2me | Theorems.Thm_GlobalTheory_T_gaussLemma_symPowMatrix_upperTriangular_placeOrder
-- name    : GlobalTheory.T.gaussLemma_symPowMatrix_upperTriangular_placeOrder
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:33:16.402074+00:00
-- url     : https://prove2.me/theorems/2ab01a93-4735-5524-99a3-c7f7b03cbbce
-- title:
--   T: gauss Lemma sym Pow Matrix upper Triangular place Order
-- statement:
--   The T construction uses the gauss Lemma sym Pow Matrix upper Triangular place Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussLemmaSymPowMatrixUpperTriangularPlaceOrderStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussLemmaSymPowMatrixUpperTriangularPlaceOrderStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussLemmaSymPowMatrixUpperTriangularPlaceOrder
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NrmCoeffProdLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussLemmaSymPowMatrixUpperTriangularPlaceOrderStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.gaussLemma_symPowMatrix_upperTriangular_placeOrder : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (P : Place k E) (m : ℕ) (A : Matrix (Fin 2) (Fin 2) E), A 1 0 = 0 → A.det ≠ 0 → ∀ (q : Fin (m + 1) → E) (c : E) (s t : Fin m → E), c ≠ 0 → (∀ j, ![s j, t j] ≠ 0) → ∑ i : Fin (m + 1), C (q i) * (C (A 0 1) + C (A 1 1) * X) ^ (i : ℕ) * C (A 0 0) ^ (m - i) = C c * ∏ j, (C (s j) * C (A 0 0) + C (t j) * (C (A 0 1) + C (A 1 1) * X)) → ordVec P ((symMat m A).mulVec q) = ord P c + ∑ j, ordVec P (A.mulVec ![s j, t j]) := by sorry
