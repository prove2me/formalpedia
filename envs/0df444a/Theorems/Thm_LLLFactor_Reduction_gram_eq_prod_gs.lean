-- Prove2me | Theorems.Thm_LLLFactor_Reduction_gram_eq_prod_gs
-- name    : LLLFactor.Reduction.gram_eq_prod_gs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:33.416083+00:00
-- url     : https://prove2.me/theorems/2b49ce90-9130-4e39-ab12-fd1ed4686a50
-- title:
--   (1.25), p. 521 — d_i = ∏_{j≤i} |b_j*|², so d_i > 0, d₀ = 1 and dₙ = d(L)²
-- statement:
--   Let $b_1,\dots,b_n\in\mathbb R^n$ be linearly independent and let $d_i=\det\big((b_j,b_l)\big)_{1\le j,l\le i}$ be the Gram determinant of the first $i$ vectors (1.24). Then for $0\le i\le n$
--   $$d_i=\prod_{j=1}^{i}|b_j^*|^2 ,$$
--   hence $d_i>0$; moreover $d_0=1$ and $d_n=d(L)^2$, where $d(L)=|\det(b_1,\dots,b_n)|$.
--
--   Identity (1.25) expresses the Gram determinants through the Gram–Schmidt lengths; it is how the potential $D=\prod_{i=1}^{n-1}d_i$ of the termination proof is controlled.
--
--   **Formalization Note.** The product is over Lean indices $0,\dots,i-1$, i.e. the paper's $j=1,\dots,i$.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 521, (1.23)–(1.25)

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

theorem gram_eq_prod_gs {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (hb : LinearIndependent ℝ b) :
    (∀ (i : ℕ) (hi : i ≤ n),
      gram b i = ∏ j : Fin i, ‖LLLFactor.RedBasis.gs b (Fin.castLE hi j)‖ ^ 2 ∧ 0 < gram b i) ∧
    gram b 0 = 1 ∧ gram b n = LLLFactor.RedBasis.latticeDet b ^ 2 := by sorry

end LLLFactor.Reduction
