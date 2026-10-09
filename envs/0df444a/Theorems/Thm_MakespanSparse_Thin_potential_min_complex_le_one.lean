-- Prove2me | Theorems.Thm_MakespanSparse_Thin_potential_min_complex_le_one
-- name    : MakespanSparse.Thin.potential_min_complex_le_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:34.22293+00:00
-- url     : https://prove2.me/theorems/11baac50-6952-4470-b250-be1c82369592
-- title:
--   P1, proof of Theorem 1, p. 6 — a [conf-IP] solution of minimum potential Φ has x_c ≤ 1 for every complex c
-- statement:
--   Let $\pi \in \mathbb{Z}^d_{>0}$, $T \in \mathbb{Z}_{>0}$, $b \in \mathbb{Z}^d_{\ge 0}$, $m \in \mathbb{Z}_{\ge 0}$, and let [conf-IP] be the configuration integer program $\sum_{c\in Q} c\,x_c = b$, $\sum_{c\in Q} x_c = m$, $x \in \mathbb{Z}^Q_{\ge 0}$. A configuration is complex if $|\operatorname{supp}(c)| > \log_2(T+1)$. The potential of a solution is
--
--   $$\Phi(x) = \sum_{c \text{ complex}} x_c\,|\operatorname{supp}(c)|.$$
--
--   Let $x$ be a feasible solution of [conf-IP] whose potential is minimum among all feasible solutions of the same instance. Then $x_c \le 1$ for every complex configuration $c$.
--
--   This is the first of the two properties of a potential-minimal solution from which the thin-solution theorem follows.
--
--   **Formalization Note** Minimality is stated as $\Phi(x) \le \Phi(y)$ for every feasible solution $y$ of the same instance $(\pi, T, b, m)$.
-- source:
--   arXiv:1604.07153v1, P1 in the proof of Theorem 1, p. 6

import Mathlib
import Definitions.Def_MakespanSparse_Thin_ConfIP

namespace MakespanSparse.Thin

/-- P1, proof of Theorem 1, arXiv:1604.07153v1, p. 6: a solution of [conf-IP] of minimum potential
uses every complex configuration at most once. -/
theorem potential_min_complex_le_one (d : ℕ) (π : Fin d → ℕ) (hπ : ∀ k, 0 < π k)
    (T : ℕ) (hT : 0 < T) (b : Fin d → ℕ) (m : ℕ)
    (x : (Fin d → ℕ) →₀ ℕ) (hx : IsConfIPSolution π T b m x)
    (hmin : ∀ y, IsConfIPSolution π T b m y → potential T x ≤ potential T y) :
    ∀ c, ¬ IsSimple T c → x c ≤ 1 := by sorry

end MakespanSparse.Thin
