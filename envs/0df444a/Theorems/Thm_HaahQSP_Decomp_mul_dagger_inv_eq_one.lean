-- Prove2me | Theorems.Thm_HaahQSP_Decomp_mul_dagger_inv_eq_one
-- name    : HaahQSP.Decomp.mul_dagger_inv_eq_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:52.647999+00:00
-- url     : https://prove2.me/theorems/780cfec3-ca7c-4b7f-8969-d748a191cb69
-- title:
--   Section 3: Laurent inverse identity for members of 𝒫ₙ
-- statement:
--   Let $F(t)=\sum_{j=-n}^{n}C_jt^j$ belong to $\mathcal P_n$, and put $F^\dagger(t)=\sum_jC_j^\dagger t^j$. For every nonzero complex $t$,
--
--   $$
--   F(t)F^\dagger(1/t)=I=F^\dagger(1/t)F(t).
--   $$
--
--   This promotes the unitary identity on the circle to a Laurent polynomial identity over the punctured complex plane.
-- source:
--   J. Haah, Product Decomposition of Periodic Functions in Quantum Signal Processing, arXiv:1806.10236v4 (2020), p. 4, §3, paragraph after Eq. (5)

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Definitions.Def_HaahQSP_Decomp_Setting

namespace HaahQSP.Decomp

open scoped Matrix

theorem mul_dagger_inv_eq_one (n : ℕ) (C : ℤ → Mat2) (hC : PSet n C) :
    ∀ t : ℂ, t ≠ 0 →
      eval n C t * daggerEval n C t⁻¹ = 1 ∧
      daggerEval n C t⁻¹ * eval n C t = 1 := by sorry

end HaahQSP.Decomp
