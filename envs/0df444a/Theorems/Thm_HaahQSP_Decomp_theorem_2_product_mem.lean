-- Prove2me | Theorems.Thm_HaahQSP_Decomp_theorem_2_product_mem
-- name    : HaahQSP.Decomp.theorem_2_product_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:29.391814+00:00
-- url     : https://prove2.me/theorems/5921768e-46db-40a6-92ad-6e00800f0785
-- title:
--   Theorem 2, first sentence: products of primitive matrices lie in ℰₙ
-- statement:
--   Let $P_1,\ldots,P_n$ be rank one orthogonal projectors on $\mathbb C^2$. Their ordered product of primitive matrices satisfies
--
--   $$
--   E_{P_1}(t)\cdots E_{P_n}(t)\in\mathcal E_n.
--   $$
--
--   This is the forward direction of the product decomposition characterization. The empty product at $n=0$ is the identity.
-- source:
--   J. Haah, Product Decomposition of Periodic Functions in Quantum Signal Processing, arXiv:1806.10236v4 (2020), p. 4, Theorem 2, first sentence

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Definitions.Def_HaahQSP_Decomp_Setting

namespace HaahQSP.Decomp

open scoped Matrix

theorem theorem_2_product_mem (n : ℕ) (Ps : Fin n → Mat2)
    (hPs : ∀ j, IsRankOneProj (Ps j)) :
    ∃ C : ℤ → Mat2, ESet n C ∧
      ∀ t : ℂ, t ≠ 0 → eval n C t = prodPrim n Ps t := by sorry

end HaahQSP.Decomp
