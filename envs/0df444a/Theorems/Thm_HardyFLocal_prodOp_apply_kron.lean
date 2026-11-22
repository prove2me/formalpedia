-- Prove2me | Theorems.Thm_HardyFLocal_prodOp_apply_kron
-- name    : HardyFLocal.prodOp_apply_kron
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T00:42:54.695857+00:00
-- url     : https://prove2.me/theorems/4b741408-3b20-40d4-95a6-2abe02f82894
-- title:
--   Action of a product superoperator on product inputs
-- statement:
--   For complex-linear superoperators on square matrices over any two finite index types, Hardy’s matrix-unit definition of their product sends the Kronecker product of two inputs to the Kronecker product of the two outputs.
-- source:
--   Hardy, arXiv:0804.0054, section 5, equation (20); matrix-unit definition of the product map.

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
open scoped Kronecker
open Classical

namespace HardyFLocal

open Classical in
theorem prodOp_apply_kron {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (Φ : Op ι) (Ψ : Op κ)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    prodOp Φ Ψ (A ⊗ₖ B) = Φ A ⊗ₖ Ψ B := by sorry

end HardyFLocal
