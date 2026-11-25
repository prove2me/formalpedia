-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_det_leading_gram_mul_upperTriangular
-- name    : GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:49:58.54273+00:00
-- url     : https://prove2.me/theorems/e517b1f0-59a0-55bf-8e55-d47251db5046
-- title:
--   HCXi: det leading gram mul upper Triangular
-- statement:
--   The HCXi construction uses the det leading gram mul upper Triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramMinorDetTriangularMul.lean#L34-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramMinorDetTriangularMul.lean#L34-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramMinorDetTriangularMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi

theorem GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ) (j : ℕ) (hj : j ≤ m), u.BlockTriangular id → (((A * u)ᴴ * (A * u)).submatrix (Fin.castLE hj) (Fin.castLE hj)).det = ((∏ b : Fin j, Complex.normSq (u (Fin.castLE hj b) (Fin.castLE hj b)) : ℝ) : ℂ) * ((Aᴴ * A).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by sorry
