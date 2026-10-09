-- Prove2me | Theorems.Thm_MakespanSparse_Thin_exists_solution_small_support
-- name    : MakespanSparse.Thin.exists_solution_small_support
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:03.475247+00:00
-- url     : https://prove2.me/theorems/95530ed1-aff7-4e1a-a50c-388405bc3e01
-- title:
--   Lemma 3, p. 5 (Eisenbrand–Shmonin) — a feasible [conf-IP] has a solution with |supp(x)| ≤ 2(d+1)log(4(d+1)T)
-- statement:
--   Let $\pi \in \mathbb{Z}^d_{>0}$, $T \in \mathbb{Z}_{>0}$, $b \in \mathbb{Z}^d_{\ge 0}$, $m \in \mathbb{Z}_{\ge 0}$, and consider the configuration integer program [conf-IP]: find $x \in \mathbb{Z}^Q_{\ge 0}$ with $\sum_{c\in Q} c\,x_c = b$ and $\sum_{c \in Q} x_c = m$, where $Q$ is the set of configurations $c \in \mathbb{Z}^d_{\ge 0}$ with $\pi\cdot c \le T$. If [conf-IP] is feasible, then it has a feasible solution $x$ with
--
--   $$|\operatorname{supp}(x)| \le 2(d+1)\log_2(4(d+1)T).$$
--
--   This is the Carathéodory-type bound of Eisenbrand and Shmonin specialised to the configuration IP; it lets an algorithm guess the support of a solution among few candidates.
--
--   **Formalization Note** $b$ and $m$ are natural numbers; the paper's $b \in \mathbb{R}^d$ adds no feasible instance. The bound is a real inequality with `Real.logb 2`.
-- source:
--   arXiv:1604.07153v1, Lemma 3, p. 5

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP

namespace MakespanSparse.Thin

/-- Lemma 3 (Eisenbrand and Shmonin), arXiv:1604.07153v1, p. 5. -/
theorem exists_solution_small_support (d : ℕ) (π : Fin d → ℕ) (hπ : ∀ k, 0 < π k)
    (T : ℕ) (hT : 0 < T) (b : Fin d → ℕ) (m : ℕ)
    (hfeas : ∃ x, IsConfIPSolution π T b m x) :
    ∃ x, IsConfIPSolution π T b m x ∧
      (x.support.card : ℝ) ≤ 2 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T) := by sorry

end MakespanSparse.Thin
