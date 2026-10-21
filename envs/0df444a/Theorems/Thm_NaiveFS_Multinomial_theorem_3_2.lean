-- Prove2me | Theorems.Thm_NaiveFS_Multinomial_theorem_3_2
-- name    : NaiveFS.Multinomial.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:53.675117+00:00
-- url     : https://prove2.me/theorems/106b2b1e-f90a-496f-9752-93678b710fd5
-- title:
--   Theorem 3.2, p. 6 — the optimal value of sparse multinomial naive Bayes is bounded by the one-dimensional relaxation: ϕ(k) ≤ ψ(k)
-- statement:
--   Let $f^\pm\in\mathbb R^m$ be the class sums with $f^\pm_i>0$, and let $k<m$. Let $\phi(k)$ be the optimal value of the sparse multinomial naive Bayes problem
--   $$\max_{\theta^\pm\in[0,1]^m}\ f^{+\top}\log\theta^++f^{-\top}\log\theta^-\ :\ \mathbf 1^\top\theta^+=\mathbf 1^\top\theta^-=1,\ \|\theta^+-\theta^-\|_0\le k.\qquad\text{(SMNB)}$$
--   Then
--   $$\phi(k)\le\psi(k):=C+\min_{\alpha\in(0,1)}s_k\big(h(\alpha)\big),\qquad\text{(USMNB)}$$
--   where $s_k$ is the sum of the top $k$ entries, $h(\alpha)=\tilde C-f^+\log\alpha-f^-\log(1-\alpha)$, $\tilde C=f^+\circ\log f^++f^-\circ\log f^--(f^++f^-)\circ\log(f^++f^-)$, and $C=(f^++f^-)^\top\log(f^++f^-)-S\log S$ with $S=\mathbf 1^\top(f^++f^-)$.
--
--   The bound replaces a nonconvex, combinatorial maximum-likelihood problem by a one-dimensional convex problem solvable by bisection.
--
--   **Formalization Note** Theorem 3.2 calls $C$ "a constant"; its value is fixed on p. 8 and is built into $\psi$. The primal reconstruction (13), the second half of Theorem 3.2, is not part of this item.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, p. 6, Theorem 3.2 (bound part), with C from p. 8

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_Model

namespace NaiveFS.Multinomial

/-- Theorem 3.2, p. 6 (bound part): `ϕ(k) ≤ ψ(k)`, with `ψ(k) = C + min_{α∈(0,1)} s_k(h(α))`
and `C = (f⁺ + f⁻)ᵀ log(f⁺ + f⁻) − S log S` (p. 8). -/
theorem theorem_3_2 {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) (hkm : k < m) :
    phi fp fm k ≤ psi fp fm k := by sorry

end NaiveFS.Multinomial
