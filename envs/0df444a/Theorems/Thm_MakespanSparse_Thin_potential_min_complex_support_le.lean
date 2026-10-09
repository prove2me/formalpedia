-- Prove2me | Theorems.Thm_MakespanSparse_Thin_potential_min_complex_support_le
-- name    : MakespanSparse.Thin.potential_min_complex_support_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:18.699296+00:00
-- url     : https://prove2.me/theorems/f910e73e-d82e-44c6-b782-7f431656c49d
-- title:
--   P2, proof of Theorem 1, p. 6 — a [conf-IP] solution of minimum potential uses at most 2(d+1)log(4(d+1)T) complex configurations
-- statement:
--   Let $\pi \in \mathbb{Z}^d_{>0}$, $T \in \mathbb{Z}_{>0}$, $b \in \mathbb{Z}^d_{\ge 0}$, $m \in \mathbb{Z}_{\ge 0}$, and let [conf-IP] be the configuration integer program $\sum_{c\in Q} c\,x_c = b$, $\sum_{c\in Q} x_c = m$, $x \in \mathbb{Z}^Q_{\ge 0}$. A configuration is complex if $|\operatorname{supp}(c)| > \log_2(T+1)$, and the potential of a solution is $\Phi(x) = \sum_{c \text{ complex}} x_c\,|\operatorname{supp}(c)|$.
--
--   Let $x$ be a feasible solution of [conf-IP] whose potential is minimum among all feasible solutions of the same instance. Then the number of complex configurations in $\operatorname{supp}(x)$ satisfies
--
--   $$\bigl|\{c \in \operatorname{supp}(x) : c \text{ complex}\}\bigr| \le 2(d+1)\log_2(4(d+1)T).$$
--
--   Together with P1 this bounds the total weight a potential-minimal solution puts on complex configurations.
--
--   **Formalization Note** Minimality is stated as $\Phi(x) \le \Phi(y)$ for every feasible solution $y$ of the same instance.
-- source:
--   arXiv:1604.07153v1, P2 in the proof of Theorem 1, p. 6

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP

namespace MakespanSparse.Thin

/-- P2, proof of Theorem 1, arXiv:1604.07153v1, p. 6: a solution of [conf-IP] of minimum potential
has at most `2(d+1) log(4(d+1)T)` complex configurations in its support. -/
theorem potential_min_complex_support_le (d : ℕ) (π : Fin d → ℕ) (hπ : ∀ k, 0 < π k)
    (T : ℕ) (hT : 0 < T) (b : Fin d → ℕ) (m : ℕ)
    (x : (Fin d → ℕ) →₀ ℕ) (hx : IsConfIPSolution π T b m x)
    (hmin : ∀ y, IsConfIPSolution π T b m y → potential T x ≤ potential T y) :
    ((x.support.filter (fun c => ¬ IsSimple T c)).card : ℝ) ≤
      2 * ((d : ℝ) + 1) * Real.logb 2 (4 * ((d : ℝ) + 1) * T) := by sorry

end MakespanSparse.Thin
