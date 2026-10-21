-- Prove2me | Theorems.Thm_FracRiccati_Radius_prop_B_1_b
-- name    : FracRiccati.Radius.prop_B_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:20.779497+00:00
-- url     : https://prove2.me/theorems/e167d657-b550-4203-b6ad-4ce03d745822
-- title:
--   Proposition B.1(b), p. 29 — for λ, μ, ν ≥ 0, a_k ≥ a⁰_k ≥ 0, hence R_ψλ,μ,ν ≤ R_ψλ,0,ν
-- statement:
--   Let $\alpha\in(0,2]$ and let $\lambda,\mu,\nu\ge0$ be real. Let $(a_k)$ and $(a^0_k)$ be the solutions of $(A_{\lambda,\mu,\nu})$ and $(A_{\lambda,0,\nu})$. Then all these coefficients are real, and for every $k\ge1$
--   $$a_k\ge a^0_k\ge0,$$
--   so that
--   $$R_{\psi_{\lambda,\mu,\nu}}\le R_{\psi_{\lambda,0,\nu}}.$$
--
--   This comparison reduces the upper bound on the radius in Theorem 3.3 (b) to the case $\mu=0$.
--
--   **Formalization Note** The real parameters are cast into $\mathbb C$ and fed to the complex recursion of the definition file; the coefficient comparison is stated on real parts, together with the vanishing of the imaginary parts. The radius is the Hadamard liminf (3.21) in $[0,\infty]$.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 29, Proposition B.1 (b)

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace FracRiccati.Radius

theorem prop_B_1_b (α : ℝ) (hα0 : 0 < α) (hα2 : α ≤ 2)
    (l m n : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) (hn : 0 ≤ n) :
    (∀ k : ℕ, 1 ≤ k →
      (coeff α l m n k).im = 0 ∧ (coeff α l 0 n k).im = 0 ∧
      (coeff α l 0 n k).re ≤ (coeff α l m n k).re ∧ 0 ≤ (coeff α l 0 n k).re) ∧
    radius α (coeff α l m n) ≤ radius α (coeff α l 0 n) := by sorry

end FracRiccati.Radius
