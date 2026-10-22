-- Prove2me | Theorems.Thm_NamikiStretch_Lossy_eq_22_coherent
-- name    : NamikiStretch.Lossy.eq_22_coherent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:43.429326+00:00
-- url     : https://prove2.me/theorems/69b82c34-ae98-4ade-b96b-e49665375564
-- title:
--   (22), p. 3 (coherent input) — the outcome weights ((1−ξ²)/2π) e^{−(1−ξ²)|α−β̄|²} integrate to 1 over dxdp
-- statement:
--   Let $\xi\in(0,1)$ and $\alpha\in\mathbb C$. For the outcome $\beta=(x+ip)/\sqrt2$ of the point $(x,p)\in\mathbb R^2$ put
--   $$w(x,p)=\frac{1-\xi^2}{2\pi}\,e^{-(1-\xi^2)|\alpha-\bar\beta|^2}.$$
--   Then $w$ is Lebesgue integrable on $\mathbb R^2$ and
--   $$\iint_{\mathbb R^2}w(x,p)\,dx\,dp=1 .$$
--   Consequently, for the coherent input $\rho=|\alpha\rangle\langle\alpha|$ and $\tilde\rho_\beta=w\,|\alpha\rangle\langle\alpha|$ (the operator (21) when $P$ is a point mass at $\alpha$), every number-basis entry satisfies $\iint\tilde\rho_\beta\,dx\,dp=\rho$, which is (22).
--
--   This normalization is what makes the averaged protocol trace preserving: the per-outcome weights of (20) form a probability density in the outcome.
--
--   **Formalization Note** The measure is Lebesgue measure on $\mathbb R\times\mathbb R$, the paper's $dx\,dp$ (equal to $2\,d^2\beta$). The paper writes the weight with $|\alpha+\beta|^2$; the integral is the same, and the weight is written with $\alpha-\bar\beta$ for consistency with the corrected (20). The statement is for a coherent input ($P$ a point mass), because the $P$ representation (19) is not a function for nonclassical states.
-- source:
--   Namiki, Teleportation stretching for single-mode Gaussian channels, arXiv:1603.05292v1, p. 3, (21)–(22) (P a point mass at α)

import Mathlib
import Definitions.Def_NamikiStretch_Lossy_Protocol

namespace NamikiStretch.Lossy

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

theorem eq_22_coherent (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (α : ℂ) :
    let w : ℝ × ℝ → ℝ := fun z => (1 - ξ ^ 2) / (2 * Real.pi) *
      Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star (outcome z)))
    (Integrable w ∧ ∫ z : ℝ × ℝ, w z = 1) ∧
    ∀ m n : ℕ, Integrable (fun z => (w z : ℂ) * coherentDensity α m n) ∧
      ∫ z : ℝ × ℝ, (w z : ℂ) * coherentDensity α m n = coherentDensity α m n := by sorry
end NamikiStretch.Lossy
