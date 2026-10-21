-- Prove2me | Theorems.Thm_FracRiccati_Radius_theorem_3_3_c
-- name    : FracRiccati.Radius.theorem_3_3_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:09.826992+00:00
-- url     : https://prove2.me/theorems/94e745f0-0962-47ed-a387-a246ca369266
-- title:
--   Theorem 3.3(c), p. 9 — for λ, ν > 0, μ ≤ 0: a_k^(λ,μ,ν) = (−1)^(k−1) a_k^(λ,−μ,ν), so the radii coincide
-- statement:
--   Let $\alpha\in(0,2]$ and let $\lambda,\nu>0$ and $\mu\le0$ be real. Writing $a^{(\lambda,\mu,\nu)}_k$ for the coefficients of $(A_{\lambda,\mu,\nu})$,
--   $$a^{(\lambda,\mu,\nu)}_k=(-1)^{k-1}\,a^{(\lambda,-\mu,\nu)}_k,\qquad k\ge1,$$
--   so that
--   $$R_{\psi_{\lambda,\mu,\nu}}=R_{\psi_{\lambda,-\mu,\nu}}.$$
--
--   This reduces the case $\mu\le0$ to $\mu\ge0$, where Proposition B.1 (b) applies.
--
--   **Formalization Note** The paper prints $(-1)^k$; at $k=1$ both coefficients equal $\nu/\Gamma(\alpha+1)$, and the proof (p. 30) sets $\tilde a_k=(-1)^{k-1}a_k$, so the sign is corrected to $(-1)^{k-1}$. Only the first sentence of Theorem 3.3 (c) is stated: its "Moreover" sentence on convergence at the radius is not formalized. The real parameters are cast into $\mathbb C$; $(-1)^{k-1}$ is a natural power with $k\ge1$.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 9, Theorem 3.3 (c), first sentence; p. 29, Proposition B.1 (c); proof p. 30

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace FracRiccati.Radius

theorem theorem_3_3_c (α : ℝ) (hα0 : 0 < α) (hα2 : α ≤ 2)
    (l m n : ℝ) (hl : 0 < l) (hn : 0 < n) (hm : m ≤ 0) :
    (∀ k : ℕ, 1 ≤ k →
      coeff α l m n k = (-1 : ℂ) ^ (k - 1) * coeff α l ((-m : ℝ) : ℂ) n k) ∧
    radius α (coeff α l m n) = radius α (coeff α l ((-m : ℝ) : ℂ) n) := by sorry

end FracRiccati.Radius
