-- Prove2me | Theorems.Thm_NaiveFS_Multinomial_theorem_3_6
-- name    : NaiveFS.Multinomial.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:05.640996+00:00
-- url     : https://prove2.me/theorems/366e5358-45c0-4d7c-86e3-abdadc342140
-- title:
--   Theorem 3.6, p. 10 — the sparse multinomial naive Bayes relaxation is tight up to four features: ψ(k−4) ≤ ϕ(k) ≤ ψ(k) ≤ ϕ(k+4)
-- statement:
--   Let $f^+,f^-\in\mathbb R^m$ be the class sums of a binary classification data set, with $f^\pm_i>0$, and let $k$ be an integer with $4\le k<m$. Let $\phi(k)$ be the optimal value of sparse multinomial naive Bayes,
--   $$\phi(k)=\max_{\theta^\pm\in[0,1]^m}\Big\{f^{+\top}\log\theta^++f^{-\top}\log\theta^-\ :\ \mathbf 1^\top\theta^+=\mathbf 1^\top\theta^-=1,\ \|\theta^+-\theta^-\|_0\le k\Big\},$$
--   and $\psi(k)=C+\min_{\alpha\in(0,1)}s_k(h(\alpha))$ the value of its convex relaxation (USMNB), with $s_k$ the top-$k$ sum, $h(\alpha)=\tilde C-f^+\log\alpha-f^-\log(1-\alpha)$, $\tilde C=f^+\circ\log f^++f^-\circ\log f^--(f^++f^-)\circ\log(f^++f^-)$ and $C=(f^++f^-)^\top\log(f^++f^-)-S\log S$, $S=\mathbf 1^\top(f^++f^-)$. Then
--   $$\psi(k-4)\le\phi(k)\le\psi(k)\le\phi(k+4).\qquad(24)$$
--
--   The relaxation is solved by a one-dimensional bisection; the theorem says that its value brackets the nonconvex sparse maximum-likelihood value up to a shift of four in the number of features, so the gap is small whenever $\psi$ varies slowly in $k$.
--
--   **Formalization Note** $\theta^\pm$ are strictly positive in the definition of $\phi$ (equivalent, since $f^\pm>0$). The constant $C$ is the one fixed on p. 8. $k<m$ is the standing assumption of §3.1 ("$k\in[m]$, with $k<m$"); $k+4$ may exceed $m$, in which case $\phi(k+4)$ is the unconstrained value. $k-4$ is natural-number subtraction, safe under $k\ge4$.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, p. 10, Theorem 3.6 (24); proof pp. 10–11

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_Model

namespace NaiveFS.Multinomial

/-- Theorem 3.6, p. 10 (Quality of Sparse Multinomial Naive Bayes Relaxation): for `k ≥ 4`,
`ψ(k − 4) ≤ ϕ(k) ≤ ψ(k) ≤ ϕ(k + 4)` (24). -/
theorem theorem_3_6 {m : ℕ} (fp fm : Fin m → ℝ) (hfp : ∀ i, 0 < fp i) (hfm : ∀ i, 0 < fm i)
    (k : ℕ) (hk : 4 ≤ k) (hkm : k < m) :
    psi fp fm (k - 4) ≤ phi fp fm k ∧ phi fp fm k ≤ psi fp fm k ∧
      psi fp fm k ≤ phi fp fm (k + 4) := by sorry

end NaiveFS.Multinomial
