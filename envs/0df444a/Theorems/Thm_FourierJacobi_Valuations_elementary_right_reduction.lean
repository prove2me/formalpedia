-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_elementary_right_reduction
-- name    : FourierJacobi.Valuations.elementary_right_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:30:31.101527+00:00
-- url     : https://prove2.me/theorems/c1b2d94d-0388-4c23-bb49-ed9025fbef34
-- title:
--   Valuations: elementary right reduction
-- statement:
--   The concrete elimination step: symplecticity forces both unwanted lower
--   entries to disappear, and the surviving middle block has determinant one.
--   Primitive-vector transitivity and the choice of an integral first column are
--   separate obligations; this theorem does not assume or assert a Cartan decomposition.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L240-L263
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L240-L263

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]

theorem FourierJacobi.Valuations.elementary_right_reduction (d b₁ b₂ c p q r s u w : K) (hd : d ≠ 0)
    (hsp : (firstColumnShape d b₁ b₂ c p q r s u w).transpose * J *
      firstColumnShape d b₁ b₂ c p q r s u w = J) :
    p * s - q * r = 1 ∧
      firstColumnShape d b₁ b₂ c p q r s u w * cartanEliminator d b₁ b₂ c =
        !![d, 0, 0, 0; 0, p, q, 0; 0, r, s, 0; 0, 0, 0, d⁻¹] := by sorry
