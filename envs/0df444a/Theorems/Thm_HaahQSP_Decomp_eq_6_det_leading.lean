-- Prove2me | Theorems.Thm_HaahQSP_Decomp_eq_6_det_leading
-- name    : HaahQSP.Decomp.eq_6_det_leading
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:49.502049+00:00
-- url     : https://prove2.me/theorems/785a26f0-d942-4a26-9b16-d2637b0b46ea
-- title:
--   Equation (6): singular extreme coefficients
-- statement:
--   Let $n>0$ and let $F(t)=\sum_{j=-n}^{n}C_jt^j$ belong to $\mathcal P_n$. Its highest and lowest coefficients are singular:
--
--   $$
--   \det C_n=0=\det C_{-n}.
--   $$
--
--   This is the determinant condition used to identify a rank one extreme coefficient in the decomposition argument.
--
--   **Formalization Note** The proof uses only membership in $\mathcal P_n$. The positive width condition is necessary because a member of $\mathcal P_0$ has determinant one.
-- source:
--   J. Haah, Product Decomposition of Periodic Functions in Quantum Signal Processing, arXiv:1806.10236v4 (2020), p. 4, Eq. (6), proof of Theorem 2

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Definitions.Def_HaahQSP_Decomp_Setting

namespace HaahQSP.Decomp

open scoped Matrix

theorem eq_6_det_leading (n : ℕ) (hn : 0 < n) (C : ℤ → Mat2)
    (hC : PSet n C) :
    Matrix.det (C (n : ℤ)) = 0 ∧
    Matrix.det (C (-(n : ℤ))) = 0 := by sorry

end HaahQSP.Decomp
