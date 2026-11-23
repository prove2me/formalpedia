-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_shift_poly
-- name    : GlobalTheory.PolyNorm.shift_poly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:34.82793+00:00
-- url     : https://prove2.me/theorems/b33107a6-fdaf-4421-b351-4e76212571e7
-- title:
--   Poly Norm: shift poly
-- statement:
--   The Poly Norm construction uses the shift poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L57-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
variable (N : ℤ[X] → ℚ) (Φ : (r : ℕ) → MvPolynomial (Fin r) ℚ)
  (hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)))
include hN

theorem GlobalTheory.PolyNorm.shift_poly (F : ℤ[X]) : ∃ p : ℚ[X], ∀ t : ℕ, N (F + t) = p.eval (t : ℚ) := by sorry
