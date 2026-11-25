-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_submatrix_mul_upperTriangular_castLE
-- name    : GlobalTheory.HCXi.submatrix_mul_upperTriangular_castLE
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:52:21.630049+00:00
-- url     : https://prove2.me/theorems/130b8cd7-3b63-4023-873f-3e850cda6ffd
-- title:
--   HCXi: submatrix mul upper Triangular cast LE
-- statement:
--   The HCXi construction uses the submatrix mul upper Triangular cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramMinorDetTriangularMul.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/GramMinorDetTriangularMul.lean#L8-L32

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

theorem GlobalTheory.HCXi.submatrix_mul_upperTriangular_castLE {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (u : Matrix (Fin m) (Fin m) ℂ) {j : ℕ} (hj : j ≤ m) (hu : u.BlockTriangular id) :
    (A * u).submatrix id (Fin.castLE hj) =
      A.submatrix id (Fin.castLE hj) * u.submatrix (Fin.castLE hj) (Fin.castLE hj) := by sorry
