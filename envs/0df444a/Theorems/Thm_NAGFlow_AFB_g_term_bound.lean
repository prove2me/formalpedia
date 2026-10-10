-- Prove2me | Theorems.Thm_NAGFlow_AFB_g_term_bound
-- name    : NAGFlow.AFB.g_term_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:04.359355+00:00
-- url     : https://prove2.me/theorems/c1f15705-86ed-4cb7-9b83-829fe3c0431b
-- title:
--   Proof of Theorem 7.3, p. 35 — g(x_{k+1}) − g(x_k) − α_k(g(v_{k+1}) − g(x_{k+1})) = (1 + α_k)g(x_{k+1}) − g(x_k) − α_kg(v_{k+1}) ≤ 0
-- statement:
--   Let $V$ be a real Hilbert space, let $(Q,h,g)$ be an instance of the composite problem (104) with constants $0\le\mu\le L$, and let $(x_k,y_k,w_k,v_k)$ with parameters $(\alpha_k,\gamma_k)$ be a run of Algorithm 4 (Semi-AFB) whose initial point $x_0$ lies in $\operatorname{dom}g$. Then for every $k$,
--   $$g(x_{k+1})-g(x_k)-\alpha_k\bigl(g(v_{k+1})-g(x_{k+1})\bigr)=(1+\alpha_k)g(x_{k+1})-g(x_k)-\alpha_kg(v_{k+1})\ \le\ 0.$$
--
--   The inequality expresses the convexity of $g$ along the convex combination $x_{k+1}=(x_k+\alpha_kv_{k+1})/(1+\alpha_k)$; it shows that the $g$-terms of (123) are nonpositive.
--
--   **Formalization Note.** The hypothesis $x_0\in\operatorname{dom}g$ is added to the page's input $x_0\in Q$. Without it $g(x_0)=+\infty$ and the inequality at $k=0$ is meaningless; with it, every $x_k$ lies in $\operatorname{dom}g$, so every value of $g$ above is finite.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 7.3, first display, p. 35

import Mathlib
import Definitions.Def_NAGFlow_AFB_Setting

namespace NAGFlow.AFB

/-- The bound on the `g`-terms of (123), p. 35 (Luo & Chen, arXiv:1909.03145v4). For a run of
Algorithm 4 for (104) that starts in `dom g` (`x₀ ∈ D`), for every `k`,
`g(x_{k+1}) − g(x_k) − α_k(g(v_{k+1}) − g(x_{k+1})) = (1 + α_k)g(x_{k+1}) − g(x_k) − α_k g(v_{k+1}) ≤ 0`. -/
theorem g_term_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (g : V → ℝ) (D Q : Set V) (μ L : ℝ)
    (hprob : IsAFBProblem h gradh g D Q μ L)
    (α γ : ℕ → ℝ) (x y w v : ℕ → V) (hrun : IsAFBRun gradh g D Q μ L α γ x y w v)
    (hx0D : x 0 ∈ D) :
    ∀ k : ℕ, g (x (k + 1)) - g (x k) - α k * (g (v (k + 1)) - g (x (k + 1))) =
        (1 + α k) * g (x (k + 1)) - g (x k) - α k * g (v (k + 1)) ∧
      (1 + α k) * g (x (k + 1)) - g (x k) - α k * g (v (k + 1)) ≤ 0 := by sorry

end NAGFlow.AFB
