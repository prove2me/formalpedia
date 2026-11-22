-- Prove2me | Theorems.Thm_MasulloAudit_norm_separating_functional_ge_inv_dist
-- name    : MasulloAudit.norm_separating_functional_ge_inv_dist
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:02:04.665694+00:00
-- url     : https://prove2.me/theorems/541c0033-12a4-4936-8988-874462a922aa
-- title:
--   A functional separating two close vectors has large norm: $\|f\|\ge 1/\|x_1-x_2\|$
-- statement:
--   Let $E$ be a normed space over $\mathbb K\in\{\mathbb R,\mathbb C\}$, let $x_1\ne x_2$ be vectors of $E$, and let $f\in E'$ be a continuous linear functional with $f(x_1)=1$ and $f(x_2)=0$. Then
--
--   $$
--   \|f\|\;\ge\;\frac{1}{\|x_1-x_2\|}.
--   $$
--
--   This is the elementary mechanism behind unbounded biorthogonal systems: when two members $x_1,x_2$ of a system come close, any functional separating them must have large norm. In the Hardy–Sobolev spaces of Masullo's draft, Chapter 10, the evaluation-type vectors $\eta_\rho$ attached to two zeta zeros $\rho_1,\rho_2$ with nearby ordinates become close, since gaps between consecutive zeros tend to $0$. So their biorthogonal functionals $\psi_\rho$ cannot be uniformly bounded, contrary to what is used in the proofs of Theorems 10.3.1.1 and 10.4.2.8 (pp. 451, 463).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Terminology 10.2.1.2(2) (p. 444), proof of Theorem 10.3.1.1 after eq. (10.3.1.18) (p. 451), and eq. (10.4.2.24) in the proof of Theorem 10.4.2.8 (p. 463).

import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.RCLike.Basic

namespace MasulloAudit

theorem norm_separating_functional_ge_inv_dist {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (f : E →L[𝕜] 𝕜) (x₁ x₂ : E) (h₁ : f x₁ = 1) (h₂ : f x₂ = 0)
    (hne : x₁ ≠ x₂) : 1 / ‖x₁ - x₂‖ ≤ ‖f‖ := by sorry

end MasulloAudit
