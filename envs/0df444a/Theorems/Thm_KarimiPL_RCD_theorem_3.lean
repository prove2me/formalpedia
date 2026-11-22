-- Prove2me | Theorems.Thm_KarimiPL_RCD_theorem_3
-- name    : KarimiPL.RCD.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:58.020796+00:00
-- url     : https://prove2.me/theorems/9922c8de-7772-43cb-8540-7710343a62c7
-- title:
--   Theorem 3, p. 5 — randomized coordinate descent under PL
-- statement:
--   Let $d\ge1$. Let $f:\mathbb R^d\to\mathbb R$ be differentiable, obey the coordinate-wise upper bound (5) with $L>0$, attain its minimum $f^*=f(x^*)$, and satisfy the PL inequality $\frac12\|\nabla f(x)\|^2\ge\mu(f(x)-f^*)$ for some $\mu>0$. From any $x_0$, independently draw $i_t$ uniformly from the $d$ coordinates at each step and set $x_{t+1}=x_t-L^{-1}\nabla_{i_t}f(x_t)e_{i_t}$. Then, for every $k\ge0$,
--
--   $$
--   \mathbb E[f(x_k)-f^*]
--   \le\left(1-\frac\mu{dL}\right)^k(f(x_0)-f^*).
--   $$
--
--   This is the expected linear rate of Theorem 3. It covers differentiable objectives satisfying PL without requiring convexity.
--
--   **Formalization Note** Independent uniform draws are represented by averaging over all words of length $k$, each with weight $d^{-k}$. The minimum value is fixed by an explicit global minimizer. The one-sided coordinate bound (5), rather than a full gradient-Lipschitz assumption, is the smoothness hypothesis.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Theorem 3, p. 5

import Mathlib
import Definitions.Def_KarimiPL_RCD_Setting
import Definitions.Def_ShiOptrates_FunctionClass

namespace KarimiPL.RCD

/-- Theorem 3, p. 5: the expected rate of randomized coordinate descent under PL. -/
theorem theorem_3 {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hcoord : CoordLipschitz f L)
    (xstar : KarimiPL.Rel.E d) (hxstar : ∀ y, f xstar ≤ f y)
    (mu : ℝ) (hmu : 0 < mu)
    (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) mu (f xstar))
    (x0 : KarimiPL.Rel.E d) :
    ∀ k : ℕ,
      expectedGap f L x0 (f xstar) k ≤
        (1 - mu / ((d : ℝ) * L)) ^ k * (f x0 - f xstar) := by sorry

end KarimiPL.RCD
