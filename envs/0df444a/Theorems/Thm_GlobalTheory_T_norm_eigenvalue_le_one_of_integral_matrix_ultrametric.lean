-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_eigenvalue_le_one_of_integral_matrix_ultrametric
-- name    : GlobalTheory.T.norm_eigenvalue_le_one_of_integral_matrix_ultrametric
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:52:32.208852+00:00
-- url     : https://prove2.me/theorems/8fb3550b-4eb9-43e3-8e55-5f6c1b181c2d
-- title:
--   T: norm eigenvalue le one of integral matrix ultrametric
-- statement:
--   The T construction uses the norm eigenvalue le one of integral matrix ultrametric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormEigenvalueLeOneOfIntegralMatrixUltrametricStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormEigenvalueLeOneOfIntegralMatrixUltrametricStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfIntegralMatrixUltrametric
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfIntegralMatrixUltrametricStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_eigenvalue_le_one_of_integral_matrix_ultrametric : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] (emb : O →+* K), (∀ c, ‖emb c‖ ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K), c ≠ 0 → (M.map emb).mulVec c = μ • c → ‖μ‖ ≤ 1 := by sorry
