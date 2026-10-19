-- Prove2me | Theorems.Thm_HaahQSP_Decomp_eq_7_leading_orth
-- name    : HaahQSP.Decomp.eq_7_leading_orth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:48.571475+00:00
-- url     : https://prove2.me/theorems/dec2e478-12f0-4e82-a058-cb170126b664
-- title:
--   Equation (7): orthogonality of extreme coefficients
-- statement:
--   Let $n>0$ and let $F(t)=\sum_{j=-n}^{n}C_jt^j$ belong to $\mathcal P_n$. Its extreme coefficients obey both matrix identities
--
--   $$
--   C_{-n}^\dagger C_n=0=C_nC_{-n}^\dagger.
--   $$
--
--   These constraints control both extreme powers when a primitive factor is removed.
--
--   **Formalization Note** The polynomial inverse identity is available for all of $\mathcal P_n$; $n>0$ separates the extreme coefficient from the constant term.
-- source:
--   J. Haah, Product Decomposition of Periodic Functions in Quantum Signal Processing, arXiv:1806.10236v4 (2020), p. 5, Eq. (7), proof of Theorem 2

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Definitions.Def_HaahQSP_Decomp_Setting

namespace HaahQSP.Decomp

open scoped Matrix

theorem eq_7_leading_orth (n : ℕ) (hn : 0 < n) (C : ℤ → Mat2)
    (hC : PSet n C) :
    (C (-(n : ℤ)))ᴴ * C (n : ℤ) = 0 ∧
    C (n : ℤ) * (C (-(n : ℤ)))ᴴ = 0 := by sorry

end HaahQSP.Decomp
