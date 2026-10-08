-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Kernel_lemma_A_4
-- name    : HyperbolicBackstepping.Kernel.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:35.420441+00:00
-- url     : https://prove2.me/theorems/6dcbe1b8-a778-48a4-adda-2124abf97a5c
-- title:
--   Lemma A.4, p. 21 — characteristic power-integral bound
-- statement:
--   Let $x_i(x,\xi,s)$ and $s_i^F(x,\xi)$ ($i=1,\dots,4$) be the characteristic curves and terminal parameters (A.9)–(A.20) of the Goursat system, and let $K_\epsilon=\max_{x\in[0,1]}\max\{1/\epsilon_1(x),1/\epsilon_2(x)\}$ (A.35). Then for every $i$, every integer $n\ge0$ and every $(x,\xi)\in\mathcal T$,
--   $$\int_0^{s_i^F(x,\xi)}x_i(x,\xi,s)^n\,ds\;\le\;K_\epsilon\,\frac{x^{n+1}}{n+1}.\qquad\text{(A.36)}$$
--
--   Each pass through a characteristic integral thus gains one power of $x$ and one factor $K_\epsilon/(n+1)$, which is what produces the factorial in the successive-approximation bounds.
--
--   **Formalization Note** The printed lemma says $n\ge1$; the statement here covers every $n\in\mathbb N$, which is stronger. The case $n=0$, i.e. $s_i^F(x,\xi)\le K_\epsilon x$, is true and is used in the base case of the induction for Proposition A.6.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, p. 21, Lemma A.4 and (A.36)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Kernel_Goursat

namespace HyperbolicBackstepping.Kernel

/-- Lemma A.4, p. 21, including the valid base case `n = 0`. -/
theorem lemma_A_4 (D : GoursatData) :
    ∀ (j : Fin 4) (n : ℕ) (x ξ : ℝ), (x, ξ) ∈ Tri →
      (∫ s in (0 : ℝ)..sF D j x ξ, (charX D j x ξ s) ^ n) ≤
        Keps D * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by sorry

end HyperbolicBackstepping.Kernel
