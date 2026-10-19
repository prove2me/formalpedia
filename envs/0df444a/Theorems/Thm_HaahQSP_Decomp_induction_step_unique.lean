-- Prove2me | Theorems.Thm_HaahQSP_Decomp_induction_step_unique
-- name    : HaahQSP.Decomp.induction_step_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:51.4802+00:00
-- url     : https://prove2.me/theorems/a0254b30-b697-47c0-bb7a-d22de37979d0
-- title:
--   Theorem 2 proof: unique degree lowering primitive factor
-- statement:
--   Let $n>0$ and let $F\in\mathcal E_n$ have degree $n$. There is a unique rank one orthogonal projector $K$ whose primitive matrix lowers the width:
--
--   $$
--   F(t)E_K(t)\in\mathcal E_{n-1}.
--   $$
--
--   This is the source's induction step, including the case where either extreme coefficient witnesses degree $n$.
--
--   **Formalization Note** The projector $K$ in this step is complementary to the final projector $P_n$ in the decomposition: $P_n=I-K$.
-- source:
--   J. Haah, Product Decomposition of Periodic Functions in Quantum Signal Processing, arXiv:1806.10236v4 (2020), p. 4, proof of Theorem 2, induction step after Theorem 2

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Definitions.Def_HaahQSP_Decomp_Setting

namespace HaahQSP.Decomp

open scoped Matrix

theorem induction_step_unique (n : ℕ) (hn : 0 < n) (C : ℤ → Mat2)
    (hC : ESet n C) (hdeg : HasDegree n C) :
    ∃! K : Mat2, IsRankOneProj K ∧
      ∃ C' : ℤ → Mat2, ESet (n - 1) C' ∧
        ∀ t : ℂ, t ≠ 0 → eval n C t * prim K t = eval (n - 1) C' t := by sorry

end HaahQSP.Decomp
