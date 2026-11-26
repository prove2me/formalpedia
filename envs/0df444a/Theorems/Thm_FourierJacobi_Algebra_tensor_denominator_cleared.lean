-- Prove2me | Theorems.Thm_FourierJacobi_Algebra_tensor_denominator_cleared
-- name    : FourierJacobi.Algebra.tensor_denominator_cleared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:43.29687+00:00
-- url     : https://prove2.me/theorems/bb49a8b8-0563-50d2-9ac3-fdbc007354c7
-- title:
--   Algebra: tensor denominator cleared
-- statement:
--   The Algebra construction uses the tensor denominator cleared property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L87-L92
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/WeylEvaluation.lean#L87-L92

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem FourierJacobi.Algebra.tensor_denominator_cleared (t a b d : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a ^ 2 * b ^ 2 * d ^ 4) * (d₁ t a b d * d₂ t a b d) =
      tensorDenominatorPolynomial t a b d := by sorry
