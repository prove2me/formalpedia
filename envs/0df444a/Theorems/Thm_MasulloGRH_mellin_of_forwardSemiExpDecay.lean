-- Prove2me | Theorems.Thm_MasulloGRH_mellin_of_forwardSemiExpDecay
-- name    : MasulloGRH.mellin_of_forwardSemiExpDecay
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-21T03:41:14.752288+00:00
-- url     : https://prove2.me/theorems/604c7981-84d2-4ae2-8f66-4f313b9a8de1
-- title:
--   Proposition B.2.1.5 — Mellin transform of a function with forward semi-exponential decay
-- statement:
--   A function $\phi$ on $\mathbb R_{>0}$ is a **Schwartz–Bruhat function**, $\phi\in\mathcal S(\mathbb R_{>0})$, if $x\mapsto\phi(e^x)$ is a Schwartz function on $\mathbb R$. Its **Mellin transform** is $M(\phi)(s)=\int_0^\infty\phi(t)\,t^s\,\frac{dt}{t}$. Let $\phi\in\mathcal S(\mathbb R_{>0})$ have **forward semi-exponential decay**: $\phi$ and its derivatives decay faster than every power of $t^{-1}$ as $t\to+\infty$. Let $0<a<b$ be real numbers.
--
--   Then the integral defining $\Phi(s)=M(\phi)(s)$ converges absolutely for every $s$ with $\operatorname{Re}(s)>0$, and:
--
--   1. $\Phi$ is holomorphic on the half-plane $\operatorname{Re}(s)>0$.
--   2. For every integer $N\ge 1$ there is a real number $C$ such that
--   $$|\Phi(\sigma+iy)|\le C\,|y|^{-N}\qquad\text{for all }\sigma\in[a,b]\text{ and all real }y\neq0 .$$
--   3. For every real $p\ge1$ and every integer $N>1$ there are real numbers $B>0$ and $C$ such that the bound of item 2 holds with this $C$ and, for every $\sigma\in[a,b]$,
--   $$\Big(\int_{\mathbb R}|\Phi(\sigma+iy)|^p\,dy\Big)^{1/p}\le\Big(B^p+C^p\int_{|y|\ge1/2}\frac{dy}{|y|^{pN}}\Big)^{1/p} .$$
--
--   The proposition gives the uniform decay of Mellin transforms on vertical strips that the contour arguments of Appendix B use.
--
--   **Formalization Note** In item 3 the source refers to the constant $C_{N,a,b}$ of item 2; the statement asserts the existence of $B$ and $C$ together, with $C$ satisfying item 2. The $L^p$ norm is written as the $p$-th root of the integral of $|\Phi|^p$, and its finiteness is stated.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.2.1, Proposition B.2.1.5, eqs. (B.2.1.3)–(B.2.1.5), p. 594

import Definitions.Def_MasulloGRH_MellinRpos

set_option autoImplicit false

namespace MasulloGRH

theorem mellin_of_forwardSemiExpDecay (ϕ : ℝ → ℂ) (hϕ : HasForwardSemiExpDecay ϕ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (∀ s : ℂ, 0 < s.re → MellinConvergent ϕ s) ∧
    DifferentiableOn ℂ (mellin ϕ) {s : ℂ | 0 < s.re} ∧
    (∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ y : ℝ, y ≠ 0 →
      ‖mellin ϕ (σ + y * Complex.I)‖ ≤ C * |y| ^ (-(N : ℤ))) ∧
    (∀ p : ℝ, 1 ≤ p → ∀ N : ℕ, 1 < N → ∃ B C : ℝ, 0 < B ∧
      (∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ y : ℝ, y ≠ 0 →
        ‖mellin ϕ (σ + y * Complex.I)‖ ≤ C * |y| ^ (-(N : ℤ))) ∧
      ∀ σ : ℝ, a ≤ σ → σ ≤ b →
        MeasureTheory.Integrable (fun y : ℝ => ‖mellin ϕ (σ + y * Complex.I)‖ ^ p) ∧
        (∫ y : ℝ, ‖mellin ϕ (σ + y * Complex.I)‖ ^ p) ^ (1 / p) ≤
          (B ^ p + C ^ p * ∫ y in {y : ℝ | 1 / 2 ≤ |y|}, |y| ^ (-(p * N))) ^ (1 / p)) := by sorry

end MasulloGRH
