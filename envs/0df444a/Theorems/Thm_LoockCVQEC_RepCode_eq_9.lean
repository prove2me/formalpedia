-- Prove2me | Theorems.Thm_LoockCVQEC_RepCode_eq_9
-- name    : LoockCVQEC.RepCode.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:16.262809+00:00
-- url     : https://prove2.me/theorems/019059a4-4f2c-4580-904e-ddea8cde25f8
-- title:
--   Eq. (9) — homodyne of the ancillas with feedforward: the conditional states of mode 1
-- statement:
--   Let $\varphi:\mathbb R^2\to\mathbb R$ be any feedforward and let $m_r(y)=\sqrt{2/(\pi e^{-2r})}\,e^{-2e^{2r}y^2}$ be the x-marginal $\int W_{\mathrm{anc}}(y,p)\,dp$ of a squeezed ancilla. Integrating the decoded state over $p_2,p_3$ with mode 1 displaced by $\varphi(x_2,x_3)$ gives the unnormalized conditional state of mode 1: writing $u=x_1+\varphi(x_2,x_3)$,
--   $$\begin{aligned}\int_{\mathbb R^2}&W_{\mathrm{dec}}(u,x_2,x_3;p_1,p_2,p_3)\,dp_2\,dp_3\\
--   ={}&(1-\gamma)^3m_r(x_2)m_r(x_3)W_{\mathrm{in}}(u,p_1)\\
--   &+\gamma(1-\gamma)^2m_r(x_2-\sqrt{\tfrac23}\bar x_2)m_r(x_3)W_{\mathrm{in}}(u-\tfrac{\bar x_2}{\sqrt3},p_1)\\
--   &+\gamma(1-\gamma)^2m_r(x_2+\tfrac{\bar x_2}{\sqrt6})m_r(x_3-\tfrac{\bar x_2}{\sqrt2})W_{\mathrm{in}}(u-\tfrac{\bar x_2}{\sqrt3},p_1)\\
--   &+\gamma(1-\gamma)^2m_r(x_2+\tfrac{\bar x_2}{\sqrt6})m_r(x_3+\tfrac{\bar x_2}{\sqrt2})W_{\mathrm{in}}(u-\tfrac{\bar x_2}{\sqrt3},p_1)\\
--   &+\gamma^2(1-\gamma)m_r(x_2-\tfrac{\bar x_2}{\sqrt6})m_r(x_3-\tfrac{\bar x_2}{\sqrt2})W_{\mathrm{in}}(u-\tfrac{2\bar x_2}{\sqrt3},p_1)\\
--   &+\gamma^2(1-\gamma)m_r(x_2-\tfrac{\bar x_2}{\sqrt6})m_r(x_3+\tfrac{\bar x_2}{\sqrt2})W_{\mathrm{in}}(u-\tfrac{2\bar x_2}{\sqrt3},p_1)\\
--   &+\gamma^2(1-\gamma)m_r(x_2+\sqrt{\tfrac23}\bar x_2)m_r(x_3)W_{\mathrm{in}}(u-\tfrac{2\bar x_2}{\sqrt3},p_1)\\
--   &+\gamma^3m_r(x_2)m_r(x_3)W_{\mathrm{in}}(u-\sqrt3\,\bar x_2,p_1)\end{aligned}$$
--   for all real $r,\gamma,\bar x_2,x_1,p_1,x_2,x_3$.
--
--   The paper's Eq. (9) is this identity with $\varphi$ replaced, in each term, by the feedforward for that error pattern ($x_2/\sqrt2$, $\sqrt{2/3}x_3$, $-\sqrt{2/3}x_3$, $2\sqrt{2/3}x_3$, $-2\sqrt{2/3}x_3$, $-\sqrt2x_2$, none, none). Since a physical feedforward can depend only on the measured $(x_2,x_3)$ and not on the unknown error pattern, it is stated here for a single function $\varphi$.
--
--   **Formalization Note** The integral is the Bochner integral over $\mathbb R\times\mathbb R$ with variables $(p_2,p_3)$; the integrand is integrable for every $\varphi$.
--
--   Differences from the source:
--   - reading: each term of (9) carries its own feedforward φ_S ("including suitable feedforward operations") → one arbitrary feedforward φ(x₂, x₃) applied to the whole decoded state before integrating over p₂, p₃; reason: a feedforward can depend only on the measured (x₂, x₃), not on the unknown error pattern; the page's terms are this identity read term by term with φ = φ_S
--   - encoding: modes and channels numbered 1, 2, 3 → Fin 3, Lean index j − 1 for the paper's mode j; reason: Lean convention; same instances
-- source:
--   van Loock, A note on quantum error correction with continuous variables, arXiv:0811.3616v1, p. 3, Eq. (9)

import Mathlib
import Definitions.Def_LoockCVQEC_RepCode_Protocol

namespace LoockCVQEC.RepCode

open Real MeasureTheory

theorem eq_9 (xb pb r γ d : ℝ) (φ : ℝ → ℝ → ℝ) (x1 p1 x2 x3 : ℝ) :
    ∫ q : ℝ × ℝ, decoded xb pb r γ d ![x1 + φ x2 x3, x2, x3] ![p1, q.1, q.2] =
      (1 - γ) ^ 3 * sqzMarg r x2 * sqzMarg r x3 * inW xb pb (x1 + φ x2 x3) p1
      + γ * (1 - γ) ^ 2 * sqzMarg r (x2 - √(2 / 3) * d) * sqzMarg r x3
          * inW xb pb (x1 + φ x2 x3 - 1 / √3 * d) p1
      + γ * (1 - γ) ^ 2 * sqzMarg r (x2 + d / √6) * sqzMarg r (x3 - d / √2)
          * inW xb pb (x1 + φ x2 x3 - 1 / √3 * d) p1
      + γ * (1 - γ) ^ 2 * sqzMarg r (x2 + d / √6) * sqzMarg r (x3 + d / √2)
          * inW xb pb (x1 + φ x2 x3 - 1 / √3 * d) p1
      + γ ^ 2 * (1 - γ) * sqzMarg r (x2 - d / √6) * sqzMarg r (x3 - d / √2)
          * inW xb pb (x1 + φ x2 x3 - 2 / √3 * d) p1
      + γ ^ 2 * (1 - γ) * sqzMarg r (x2 - d / √6) * sqzMarg r (x3 + d / √2)
          * inW xb pb (x1 + φ x2 x3 - 2 / √3 * d) p1
      + γ ^ 2 * (1 - γ) * sqzMarg r (x2 + √(2 / 3) * d) * sqzMarg r x3
          * inW xb pb (x1 + φ x2 x3 - 2 / √3 * d) p1
      + γ ^ 3 * sqzMarg r x2 * sqzMarg r x3 * inW xb pb (x1 + φ x2 x3 - √3 * d) p1 := by sorry

end LoockCVQEC.RepCode
