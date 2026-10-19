-- Prove2me | Theorems.Thm_HaahQSP_Decomp_leading_ne_zero_iff
-- name    : HaahQSP.Decomp.leading_ne_zero_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:50.484998+00:00
-- url     : https://prove2.me/theorems/831123fd-7fba-4bcd-8b6a-14a78776566c
-- title:
--   Theorem 2 proof: both extreme coefficients are nonzero together
-- statement:
--   If $F(t)=\sum_{j=-n}^{n}C_jt^j$ belongs to $\mathcal E_n$ and has degree $n$, then
--
--   $$
--   C_n\ne0\quad\Longleftrightarrow\quad C_{-n}\ne0.
--   $$
--
--   This relation removes the need to assume $C_n\ne0$ when stating the final projector formula.
-- source:
--   J. Haah, Product Decomposition of Periodic Functions in Quantum Signal Processing, arXiv:1806.10236v4 (2020), p. 5, proof of Theorem 2, paragraph beginning ‘Actually’

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Definitions.Def_HaahQSP_Decomp_Setting

namespace HaahQSP.Decomp

open scoped Matrix

theorem leading_ne_zero_iff (n : ℕ) (C : ℤ → Mat2)
    (hC : ESet n C) (hdeg : HasDegree n C) :
    C (n : ℤ) ≠ 0 ↔ C (-(n : ℤ)) ≠ 0 := by sorry

end HaahQSP.Decomp
