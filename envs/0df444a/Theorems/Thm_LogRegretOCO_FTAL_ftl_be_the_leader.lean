-- Prove2me | Theorems.Thm_LogRegretOCO_FTAL_ftl_be_the_leader
-- name    : LogRegretOCO.FTAL.ftl_be_the_leader
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:39:56.8707+00:00
-- url     : https://prove2.me/theorems/3e5e2b9d-b1ea-46de-b58e-afd365aa1273
-- title:
--   Lemma 10 — Follow the Leader is no worse than Be the Leader (index corrected)
-- statement:
--   Let $f_1, f_2, \dots$ be cost functions on $\mathbb{R}^n$ and let $x_1, x_2, \dots$ be a run of Follow the Leader over $P$, i.e. $x_t \in \arg\min_{x \in P} \sum_{\tau=1}^{t-1} f_\tau(x)$ for every $t \ge 1$. Then for every $T$ and every $u \in P$,
--
--   $$
--   \sum_{t=1}^T f_t(x_t) - \sum_{t=1}^T f_t(u) \le \sum_{t=1}^T f_t(x_t) - \sum_{t=1}^T f_t(x_{t+1}).
--   $$
--
--   Equivalently, the "Be the Leader" sequence, which plays in round $t$ the minimiser $x_{t+1}$ of the costs up to and including round $t$, has cost at most that of the best fixed point in hindsight. The lemma reduces bounding the regret of FTL to bounding how much consecutive leaders differ.
--
--   **Formalization Note** The paper prints $x_t = \arg\min_{x \in P} \sum_{\tau=1}^{t} f_\tau(x)$. With that index the lemma is false already for $T = 1$ (take $P = [0,1]$, $f_1(x) = x$, $f_2(x) = -2x$: then $x_2 = 1$ and $f_1(x_2) = 1 > 0 = \min f_1$). The paper's proof ("for $T = 1$ the two are equal by definition") and every use of the lemma (Theorem 5) need $x_t = \arg\min_{x\in P}\sum_{\tau=1}^{t-1} f_\tau(x)$, the Follow the Leader rule, which is what is stated here. The paper's "$-\min_{x \in P}$" is encoded as "for every comparator $u \in P$".
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 190, Lemma 10 (Appendix 1)

import Mathlib
import Definitions.Def_LogRegretOCO_FTAL_IsFTLRun

namespace LogRegretOCO.FTAL
theorem ftl_be_the_leader {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : IsFTLRun P f x) (T : ℕ) :
    ∀ u ∈ P,
      ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t u
        ≤ ∑ t ∈ Finset.Icc 1 T, f t (x t) - ∑ t ∈ Finset.Icc 1 T, f t (x (t + 1)) := by sorry
end LogRegretOCO.FTAL
