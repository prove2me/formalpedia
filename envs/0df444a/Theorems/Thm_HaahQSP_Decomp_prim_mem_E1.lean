-- Prove2me | Theorems.Thm_HaahQSP_Decomp_prim_mem_E1
-- name    : HaahQSP.Decomp.prim_mem_E1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:26.655932+00:00
-- url     : https://prove2.me/theorems/6ddc8cb3-9de8-4f05-96ca-e62c2e85ef6e
-- title:
--   Definition 1 remark: primitive matrices belong to ℰ₁
-- statement:
--   Let $P$ be a rank one orthogonal projector on $\mathbb C^2$. Then the primitive matrix $E_P(t)=tP+t^{-1}(I-P)$ is a member of $\mathcal E_1$:
--
--   $$
--   E_P\in\mathcal E_1.
--   $$
--
--   This establishes that a single primitive factor has the required unitarity and exponent parity.
--
--   **Formalization Note** Equation (2) specifies rank one. Definition 1's unrestricted phrase “any orthogonal projector” is false for $P=0$ and $P=I$, so the rank one condition is explicit.
-- source:
--   J. Haah, Product Decomposition of Periodic Functions in Quantum Signal Processing, arXiv:1806.10236v4 (2020), p. 4, Definition 1, remark after Eq. (5)

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Int.Interval
import Definitions.Def_HaahQSP_Decomp_Setting

namespace HaahQSP.Decomp

open scoped Matrix

theorem prim_mem_E1 (P : Mat2) (hP : IsRankOneProj P) :
    ∃ C : ℤ → Mat2, ESet 1 C ∧ ∀ t : ℂ, t ≠ 0 → eval 1 C t = prim P t := by sorry

end HaahQSP.Decomp
