-- Prove2me | Theorems.Thm_MasulloGRH_mellin_uniform_riemann_lebesgue
-- name    : MasulloGRH.mellin_uniform_riemann_lebesgue
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:42:12.333186+00:00
-- url     : https://prove2.me/theorems/c7e9f8db-7645-4a3c-a0b4-38e9e682d71a
-- title:
--   Proposition B.2.2.3 — Uniform Riemann–Lebesgue for Mellin transforms on a closed strip
-- statement:
--   A function $\phi$ on $\mathbb R_{>0}$ is a **Schwartz–Bruhat function**, $\phi\in\mathcal S(\mathbb R_{>0})$, if $x\mapsto\phi(e^x)$ is a Schwartz function on $\mathbb R$. Its **Mellin transform** is $M(\phi)(s)=\int_0^\infty\phi(t)\,t^s\,\frac{dt}{t}$. Let $a<b$ be real numbers and let $\phi\in\mathcal S(\mathbb R_{>0})$ be such that $t^\sigma\phi\in\mathcal S(\mathbb R_{>0})$ for every $\sigma\in[a,b]$.
--
--   Then:
--
--   1. $M(\phi)$ is continuous on the closed strip $\mathbb C_{[a,b]}$, its restriction $y\mapsto M(\phi)(\sigma+iy)$ to each vertical line with $\sigma\in[a,b]$ is a Schwartz function of $y$, and $M(\phi)$ is holomorphic on the open strip $\mathbb C_{(a,b)}$.
--   2. For every integer $N\ge1$ there are $C>0$ and $Y$ such that
--   $$|M(\phi)(\sigma+iy)|\le\frac{C}{|y|^N}\qquad\text{for all }\sigma\in[a,b]\text{ and all real }y\text{ with }|y|\ge Y .$$
--
--   In particular $M(\phi)$ is uniformly Schwartz over every open vertical strip contained in $\mathbb C_{[a,b]}$, which is the hypothesis of the Asymptotic Cauchy Integral Formula.
--
--   **Formalization Note** The function $t^\sigma\phi$ is `powMul σ ϕ`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.2.2, Proposition B.2.2.3 (Uniform Riemann-Lebesgue - I), eq. (B.2.2.2), p. 601

import Definitions.Def_MasulloGRH_MellinRpos

set_option autoImplicit false

namespace MasulloGRH

theorem mellin_uniform_riemann_lebesgue (a b : ℝ) (hab : a < b) (ϕ : ℝ → ℂ)
    (hϕ : IsSchwartzRpos ϕ) (h : ∀ σ : ℝ, a ≤ σ → σ ≤ b → IsSchwartzRpos (powMul σ ϕ)) :
    ContinuousOn (mellin ϕ) (closedStrip a b) ∧
    (∀ σ : ℝ, a ≤ σ → σ ≤ b →
      ∃ g : SchwartzMap ℝ ℂ, ∀ y : ℝ, g y = mellin ϕ (σ + y * Complex.I)) ∧
    DifferentiableOn ℂ (mellin ϕ) (openStrip a b) ∧
    (∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 0 < C ∧ ∃ Y : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ |s.im| →
      ‖mellin ϕ s‖ ≤ C / |s.im| ^ N) := by sorry

end MasulloGRH
