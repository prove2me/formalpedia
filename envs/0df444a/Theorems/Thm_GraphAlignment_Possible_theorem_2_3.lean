-- Prove2me | Theorems.Thm_GraphAlignment_Possible_theorem_2_3
-- name    : GraphAlignment.Possible.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:15.430593+00:00
-- url     : https://prove2.me/theorems/be7e98e6-afed-4464-8f3c-693af773f812
-- title:
--   Theorem 2.3, pp. 8–9 — under (6) some algorithm recovers a fraction α of the planted alignment with probability → 1
-- statement:
--   Let $0 < \alpha < 1$ and let $q = q_n$, $s = s_n$ satisfy $0 \le q_n < s_n \le 1$ for every $n$. Suppose there exist $\beta > 0$ and $\gamma > 0$ such that, for all large enough $n$,
--   $$nqs \ge \max\Big\{20,\ 84\log\frac{2}{1-\alpha},\ \frac{16}{\min(\gamma,\beta)(1-\alpha)}\Big\},\quad s > \frac{8}{1-\alpha}\,q,\quad \frac{2q(1-s^2)}{s} \le n^{-\beta},\quad qs \le n^{-2\gamma}. \quad (6)$$
--   Then there exists an algorithm which, from the two observed graphs $G_A$ and $G_B$ of the correlated Erdős–Rényi model $(n, q_n, s_n)$, returns a permutation $\hat\pi$ such that, whatever the planted permutations $\pi^*_n$,
--   $$\mathbb P\big[\beta(\hat\pi, \pi^*_n) \ge \alpha\big] \longrightarrow 1 \qquad (n \to \infty).$$
--
--   This is the possibility result of the paper: partial recovery of the alignment is achievable in the sparse regime $nqs = \Theta(1)$, provided $nqs$ exceeds an explicit constant depending on $\alpha$ and the sparsity exponents.
--
--   **Formalization Note** An algorithm is a family of maps, one for each $n$, from the observed pair of adjacency matrices $(A, B)$ to a permutation of $\{1,\dots,n\}$. It is chosen once $\alpha$ and the sequences $q_n, s_n$ are fixed, and **before** the planted permutations: it may depend on $n, q_n, s_n, \alpha$ but not on $\pi^*$ or on the hidden graph $G_{B'}$. The theorem does not say how $\pi^*$ is drawn; requiring the limit for every sequence $\pi^*_n$ covers the uniform case. A deterministic algorithm suffices for an existence statement. "Exponential-time" is not formalized. The logarithm is natural.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, pp. 8–9, Theorem 2.3, (6)

import Mathlib
import Definitions.Def_GraphAlignment_Possible_Setting

namespace GraphAlignment.Possible

open Filter Topology

theorem theorem_2_3 (α : ℝ) (hα : 0 < α ∧ α < 1) (q s : ℕ → ℝ)
    (hqs : ∀ n, 0 ≤ q n ∧ q n < s n ∧ s n ≤ 1)
    (h6 : ∃ βe > 0, ∃ γe > 0, ∀ᶠ n : ℕ in atTop, Cond6 α βe γe n (q n) (s n)) :
    ∃ alg : ∀ n : ℕ, Obs n → Equiv.Perm (Fin n),
      ∀ πstar : ∀ n : ℕ, Equiv.Perm (Fin n),
        Tendsto (fun n : ℕ => prob (q n) (s n)
            (fun ω : Config n => α ≤ overlap (alg n (A ω, B (πstar n) ω)) (πstar n)))
          atTop (𝓝 1) := by sorry

end GraphAlignment.Possible
