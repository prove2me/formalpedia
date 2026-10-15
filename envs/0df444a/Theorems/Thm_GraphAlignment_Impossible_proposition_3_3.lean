-- Prove2me | Theorems.Thm_GraphAlignment_Impossible_proposition_3_3
-- name    : GraphAlignment.Impossible.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:39.465059+00:00
-- url     : https://prove2.me/theorems/83b0ebb7-1523-47b8-8ef5-29ec54e05f26
-- title:
--   Proposition 3.3, p. 11 — M/M_α = Ω((nα)!), posed with ⌈nα⌉!
-- statement:
--   Let $\alpha_n\in(0,1)$ for every $n$, let $M=n!$ and $M_{\alpha}=\max_{\pi^*}|\{\pi\mid\beta(\pi,\pi^*)\ge\alpha_n\}|$ be as in Corollary 3.2. Then there is a constant $C>0$ such that, for all sufficiently large $n$,
--   $$
--   \frac{n!}{M_{\alpha_n}}\;\ge\;C\cdot\lceil n\alpha_n\rceil! ,
--   $$
--   that is, $M/M_\alpha=\Omega((n\alpha)!)$ in the sense of §2.3.
--
--   The ratio $M/M_\alpha$ is the effective number of well-separated hypotheses in the Fano bound; this proposition says it grows like a factorial of the number of vertices to be matched.
--
--   **Formalization Note** For non-integer $n\alpha$ the page's $(n\alpha)!$ is read as $\lceil n\alpha\rceil!$, the quantity of the paper's own proof ($O(1/\lceil n\alpha\rceil!)$, p. 12). $\alpha$ may depend on $n$. The constant $C$ is fixed before $n$ (the definition of $\Omega$ of §2.3).
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 11, Proposition 3.3 (proof pp. 11–12)

import Mathlib
import Definitions.Def_GraphAlignment_Impossible_Setting

namespace GraphAlignment.Impossible

open Filter

theorem proposition_3_3 (α : ℕ → ℝ) (hα : ∀ n, 0 < α n ∧ α n < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C * ((⌈(n : ℝ) * α n⌉₊).factorial : ℝ) ≤ (n.factorial : ℝ) / (Mα n (α n) : ℝ) := by sorry

end GraphAlignment.Impossible
