-- Prove2me | Theorems.Thm_MakespanSparse_Thin_thin_solution
-- name    : MakespanSparse.Thin.thin_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:09.289189+00:00
-- url     : https://prove2.me/theorems/9aefc17e-5d78-4121-9071-4c4246f122a8
-- title:
--   Theorem 1, p. 3 — a feasible [conf-IP] has a thin solution: |supp(x)| ≤ 4(d+1)log(4(d+1)T), complex configurations used at most once, in total ≤ 2(d+1)log(4(d+1)T)
-- statement:
--   Let $\pi \in \mathbb{Z}^d_{>0}$ be a vector of job sizes and $T \in \mathbb{Z}_{>0}$ a capacity, and let $Q = \{c \in \mathbb{Z}^d_{\ge 0} : \pi\cdot c \le T\}$ be the set of configurations. A configuration $c$ is *simple* if $|\operatorname{supp}(c)| \le \log_2(T+1)$ and *complex* otherwise; $Q_c$ denotes the set of complex configurations. For $b \in \mathbb{Z}^d_{\ge 0}$ and $m \in \mathbb{Z}_{\ge 0}$, the configuration integer program [conf-IP] asks for $x \in \mathbb{Z}^Q_{\ge 0}$ with
--
--   $$\sum_{c\in Q} c\,x_c = b, \qquad \sum_{c\in Q} x_c = m.$$
--
--   **Theorem (Thin solutions).** Assume that [conf-IP] is feasible. Then there exists a feasible solution $x$ to [conf-IP] such that:
--
--   1. if $x_c > 1$ then the configuration $c$ is simple,
--   2. the support of $x$ satisfies $|\operatorname{supp}(x)| \le 4(d+1)\log(4(d+1)T)$, and
--   3. $\sum_{c \in Q_c} x_c \le 2(d+1)\log(4(d+1)T)$,
--
--   where $\log = \log_2$.
--
--   In scheduling terms: $m$ identical machines can process the job multiset $b$ within makespan $T$ by a schedule that uses only $O(d\log(dT))$ distinct machine packings, and all but $O(d \log (dT))$ machines carry simple packings. Since there are far fewer simple configurations than configurations, this is what lets the support of a solution be guessed quickly in the paper's EPTAS for $P\|C_{\max}$.
--
--   **Formalization Note** Configurations are vectors in $\mathbb{N}^d$ and a solution is a finitely supported function on them vanishing off $Q$. The right-hand side $b$ is taken in $\mathbb{N}^d$: the paper writes $b \in \mathbb{R}^d$, but only nonnegative integer vectors are feasible. Item 3 is the sum of the multiplicities over complex configurations, not their number. All bounds are real inequalities with `Real.logb 2`.
-- source:
--   arXiv:1604.07153v1, Theorem 1, p. 3 (proof p. 6)

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP

namespace MakespanSparse.Thin

/-- Theorem 1 (Thin solutions), arXiv:1604.07153v1, p. 3. -/
theorem thin_solution (d : ℕ) (π : Fin d → ℕ) (hπ : ∀ k, 0 < π k) (T : ℕ) (hT : 0 < T)
    (b : Fin d → ℕ) (m : ℕ)
    (hfeas : ∃ x, IsConfIPSolution π T b m x) :
    ∃ x, IsConfIPSolution π T b m x ∧
      (∀ c, 1 < x c → IsSimple T c) ∧
      (x.support.card : ℝ) ≤ 4 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T) ∧
      ((∑ c ∈ x.support.filter (fun c => ¬ IsSimple T c), x c : ℕ) : ℝ) ≤
        2 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T) := by sorry

end MakespanSparse.Thin
