-- Prove2me | Theorems.Thm_MLRPCake_EnvyFree_proposition_1
-- name    : MLRPCake.EnvyFree.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:25.352736+00:00
-- url     : https://prove2.me/theorems/9551f6c4-00f5-443e-8cb9-b66e6fb60933
-- title:
--   Proposition 1, p. 11 — with λ-Lipschitz queries the ripple map RD_n is λ^{2(n−1)}-Lipschitz
-- statement:
--   Let $\mathcal C=\langle[n],\{f_i\}_i\rangle$ be a cake-division instance with $n\ge 2$ agents whose cut and eval queries are $\lambda$-Lipschitz (in the $\infty$-norm) for some $\lambda\ge1$. Let $\mathrm{RD}_n$ be the ripple map of recursion (1), which sends the first cut point $x_1=x$ to the last cut point $x_n$ determined by the ripple equalities. Then for all $x,x'\in[0,1]$,
--   $$|\mathrm{RD}_n(x')-\mathrm{RD}_n(x)|\le\lambda^{2(n-1)}\,|x'-x|.$$
--
--   Continuity of $\mathrm{RD}_n$ yields the existence of $\delta$-ripple divisions through the intermediate value theorem (Lemma 2). The explicit Lipschitz constant is what makes the binary search of Algorithm 1 run in time polynomial in $\log\lambda$ (Lemma 4).
--
--   **Formalization Note** $\lambda\ge1$ is the paper's standing assumption (p. 8). The cake-division instance assumptions (nonnegative, bounded, integrable, normalized densities) are included. MLRP is not assumed, as on the page.
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, p. 11, Proposition 1 (proof in Appendix B, pp. 30–31)

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model

namespace MLRPCake.EnvyFree

/-- Proposition 1, p. 11: if the cut and eval queries are `λ`-Lipschitz, then the ripple map
`RD_n` is `λ^{2(n-1)}`-Lipschitz on `[0,1]`. -/
theorem proposition_1 (n : ℕ) (f : Fin n → ℝ → ℝ) (lam : ℝ) (hn : 2 ≤ n) (hf : IsInstance f)
    (hlam : 1 ≤ lam) (hL : QueriesLipschitz f lam) :
    ∀ x x' : ℝ, x ∈ Set.Icc (0:ℝ) 1 → x' ∈ Set.Icc (0:ℝ) 1 →
      |rd f n x' - rd f n x| ≤ lam ^ (2 * (n - 1)) * |x' - x| := by sorry

end MLRPCake.EnvyFree
