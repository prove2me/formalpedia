-- Prove2me | Theorems.Thm_HaahQSP_Decomp_eq_8_reduce_degree
-- name    : HaahQSP.Decomp.eq_8_reduce_degree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:49.151044+00:00
-- url     : https://prove2.me/theorems/e81ca327-1d73-4e46-8ace-ed0f84bc7112
-- title:
--   Equation (8): the rank one degree reduction step
-- statement:
--   Let $n>0$, $F(t)=\sum_{j=-n}^{n}C_jt^j\in\mathcal E_n$, and $C_n\ne0$. There is a unique rank one orthogonal projector $K$ satisfying $C_nK=0$. With $L=I-K$, the product has lower width:
--
--   $$
--   F(t)\bigl(tK+t^{-1}L\bigr)\in\mathcal E_{n-1}.
--   $$
--
--   This is the source's degree lowering claim associated with the expansion in equation (8).
--
--   **Formalization Note** The coefficient $C_n\ne0$ selects the case treated explicitly on the page. The opposite case is handled by the later induction step.
-- source:
--   J. Haah, Product Decomposition of Periodic Functions in Quantum Signal Processing, arXiv:1806.10236v4 (2020), p. 5, proof of Theorem 2, Eq. (8)

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Definitions.Def_HaahQSP_Decomp_Setting

namespace HaahQSP.Decomp

open scoped Matrix

theorem eq_8_reduce_degree (n : ℕ) (hn : 0 < n) (C : ℤ → Mat2)
    (hC : ESet n C) (hCn : C (n : ℤ) ≠ 0) :
    ∃ K : Mat2, IsRankOneProj K ∧ C (n : ℤ) * K = 0 ∧
      (∀ K' : Mat2, IsRankOneProj K' → C (n : ℤ) * K' = 0 → K' = K) ∧
      ∃ C' : ℤ → Mat2, ESet (n - 1) C' ∧
        ∀ t : ℂ, t ≠ 0 → eval n C t * prim K t = eval (n - 1) C' t := by sorry

end HaahQSP.Decomp
