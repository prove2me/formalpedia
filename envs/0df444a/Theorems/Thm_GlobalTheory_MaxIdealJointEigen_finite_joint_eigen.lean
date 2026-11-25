-- Prove2me | Theorems.Thm_GlobalTheory_MaxIdealJointEigen_finite_joint_eigen
-- name    : GlobalTheory.MaxIdealJointEigen.finite_joint_eigen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:47:35.588031+00:00
-- url     : https://prove2.me/theorems/38487e09-b1ee-576c-81ea-8ddad6b91ba0
-- title:
--   Max Ideal Joint Eigen: finite joint eigen
-- statement:
--   The Max Ideal Joint Eigen construction uses the finite joint eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalIdealEqJointEigen.lean#L48-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MaximalIdealEqJointEigen.lean#L48-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfIntegralMatrixUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealEqJointEigen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory GlobalTheory.MaxIdealJointEigen

theorem GlobalTheory.MaxIdealJointEigen.finite_joint_eigen {K I : Type} [Field K] {n : ℕ} (T : I → Matrix (Fin n) (Fin n) K) :
    {θ : I → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, (T i).mulVec c = θ i • c}.Finite := by sorry
