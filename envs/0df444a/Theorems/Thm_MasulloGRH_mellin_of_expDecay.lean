-- Prove2me | Theorems.Thm_MasulloGRH_mellin_of_expDecay
-- name    : MasulloGRH.mellin_of_expDecay
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:41:36.286427+00:00
-- url     : https://prove2.me/theorems/1e86f11e-4ea6-476a-82f1-7527d8cd8c81
-- title:
--   Proposition B.2.1.9 — Mellin transform of a function with exponential decay
-- statement:
--   A function $\phi$ on $\mathbb R_{>0}$ is a **Schwartz–Bruhat function**, $\phi\in\mathcal S(\mathbb R_{>0})$, if $x\mapsto\phi(e^x)$ is a Schwartz function on $\mathbb R$. Its **Mellin transform** is $M(\phi)(s)=\int_0^\infty\phi(t)\,t^s\,\frac{dt}{t}$. Let $\phi\in\mathcal S_E(\mathbb R_{>0})$ have **exponential decay**: $\phi$ and its derivatives decay faster than every power of $e^{-|\log t|}$ as $|\log t|\to\infty$.
--
--   Then the integral defining $\Phi(s)=M(\phi)(s)$ converges absolutely for every $s\in\mathbb C$, and:
--
--   1. $\Phi$ is entire.
--   2. For all real $a<b$ and every integer $N\ge1$ there is a real number $C$ such that
--   $$|\Phi(\sigma+iy)|\le C\,|y|^{-N}\qquad\text{for all }\sigma\in[a,b]\text{ and all real }y\ne0 .$$
--   3. If $\phi$ vanishes on $(0,1]$, then for every real $b$ and every integer $N\ge1$ the constant can be chosen independently of the lower end of the strip: there is $C$ with $|\Phi(\sigma+iy)|\le C|y|^{-N}$ for all $\sigma\le b$ and all $y\ne0$.
--
--   Entire Mellin transforms with rapid decay on vertical strips are the multipliers used in the contour integrals of Appendix B.
--
--   **Formalization Note** The source states item 3 as: the constant depends on $N$, $b$ and $\phi$ but not on $a$. Part (3) of the source ($L^p$ bounds) and the membership $\Phi\in H^p(\mathbb C_{<b})$ are not part of this statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.2.1, Proposition B.2.1.9, eqs. (B.2.1.26)–(B.2.1.27), pp. 598–599, parts (1), (2) and the first assertion of (4)

import Definitions.Def_MasulloGRH_MellinRpos

set_option autoImplicit false

namespace MasulloGRH

theorem mellin_of_expDecay (ϕ : ℝ → ℂ) (hϕ : HasExpDecay ϕ) :
    (∀ s : ℂ, MellinConvergent ϕ s) ∧
    Differentiable ℂ (mellin ϕ) ∧
    (∀ a b : ℝ, a < b → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ y : ℝ, y ≠ 0 →
      ‖mellin ϕ (σ + y * Complex.I)‖ ≤ C * |y| ^ (-(N : ℤ))) ∧
    ((∀ t : ℝ, 0 < t → t ≤ 1 → ϕ t = 0) →
      ∀ b : ℝ, ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ σ : ℝ, σ ≤ b → ∀ y : ℝ, y ≠ 0 →
        ‖mellin ϕ (σ + y * Complex.I)‖ ≤ C * |y| ^ (-(N : ℤ))) := by sorry

end MasulloGRH
