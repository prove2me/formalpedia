-- Prove2me | Theorems.Thm_GraphAlignment_Possible_eq_10
-- name    : GraphAlignment.Possible.eq_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:59.306184+00:00
-- url     : https://prove2.me/theorems/b1a3e0f0-5edb-418b-b186-7cacad696445
-- title:
--   (10), p. 15 — |S¹₂| ≤ n(1 − ε) and |S̄²₂| ≤ C(n,2) − C(nε,2) ≤ n²(1 − ε²)/2
-- statement:
--   Let $n \ge 1$, let $p$ be a permutation of $\{1,\dots,n\}$ with $m$ fixed points, and let $\epsilon = m/n$. With $S^1_2$ (ordered pairs $(i,j)$, $i\ne j$, $p(i)\ne i$, swapped by $p$) and $\bar S^2_2$ (unordered pairs $\{i,j\}$, $i \ne j$, with $\{p(i),p(j)\} \ne \{i,j\}$) as in §4.1.2,
--   $$|S^1_2| \le n(1-\epsilon) \qquad\text{and}\qquad |\bar S^2_2| \le \binom n2 - \binom{n\epsilon}2 \le \frac{n^2}{2}(1-\epsilon^2).$$
--
--   These counts bound the number of terms in the decomposition of $\sum_{(i,j)\in S_2} A_{ij}B'_{p(i)p(j)}$ used in Proposition 4.4.
--
--   **Formalization Note** The statement is for an arbitrary permutation $p$ (the paper's $p$ relates a candidate to the planted permutation; its definition $p = \pi\circ\pi^{*-1}$ is a slip for $\pi^{*-1}\circ\pi$, which has the same number of fixed points). $\binom{n\epsilon}{2}$ is $\binom m2$, and the differences are computed in $\mathbb R$ after casting the binomial coefficients. The hypothesis $n \ge 1$ makes $\epsilon = m/n$ meaningful.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, p. 15, §4.1.2, (10)

import Mathlib
import Definitions.Def_GraphAlignment_Possible_PermutationSets

namespace GraphAlignment.Possible

theorem eq_10 (n : ℕ) (hn : 0 < n) (p : Equiv.Perm (Fin n)) :
    let m : ℕ := numFixed p
    let ε : ℝ := (m : ℝ) / n
    ((S12 p).card : ℝ) ≤ n * (1 - ε) ∧
      ((Sbar22 p).card : ℝ) ≤ (n.choose 2 : ℝ) - (m.choose 2 : ℝ) ∧
      (n.choose 2 : ℝ) - (m.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 * (1 - ε ^ 2) := by sorry

end GraphAlignment.Possible
