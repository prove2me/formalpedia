-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_polynomial_decay
-- name    : OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.polynomial_decay
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:58:19.903186+00:00
-- url     : https://prove2.me/theorems/61ad03d9-dd2a-46e6-96b0-6f00a880637b
-- title:
--   Uniform non-stationary phase decay for oscillatory integrals with quadratic phase
-- statement:
--   For a function $g:\mathbb{R}\to\mathbb{C}$, real parameters $t,u$ and an integer $k\ge 0$, consider the quadratic phase and the associated oscillatory integral
--   $$
--   \varphi_{t,u}(x)=e^{2\pi i\,(t x^2/2-u x)},\qquad I_k(g;t,u)=\int_{\mathbb{R}}\frac{g(x)}{(t x-u)^k}\,\varphi_{t,u}(x)\,dx .
--   $$
--   Write $\operatorname{tsupp} g$ for the closed support of $g$.
--
--   Let $l\ge 0$ be an integer and let $c>0$ and $B\ge 0$ be real numbers. Then for every infinitely differentiable, compactly supported $g:\mathbb{R}\to\mathbb{C}$ and every integer $k\ge0$ there is a constant $C\ge 0$ with the following property: whenever $t,u,M\in\mathbb{R}$ satisfy
--   $$
--   M>0,\qquad |t|\le BM,\qquad |tx-u|\ge cM\ \text{ for all } x\in\operatorname{tsupp} g,
--   $$
--   we have
--   $$
--   M^{k+l}\,\bigl|I_k(g;t,u)\bigr|\le C .
--   $$
--
--   The derivative of the phase $2\pi(tx^2/2-ux)$ is $2\pi(tx-u)$, so the last hypothesis says that the phase has no stationary point on the support of $g$ and that its derivative is at least $2\pi cM$ in absolute value there. The theorem is a quantitative non-stationary phase estimate: the integral is $O(M^{-k-l})$ for every $l$, with a constant depending on $g,k,l,c,B$ but not on the parameters $t,u,M$. The case $k=0$ gives $\int g\,\varphi_{t,u}=O(M^{-l})$, which is how the result is used to bound Fourier coefficients of chirps away from their stationary window.
--
--   **Formalization Note** The integral is `osc g t u k`, built from the amplitude `amp g t u k x = g x / (t*x-u)^k` and the phase `phase t u x`. Lean's convention that division by zero gives $0$ plays no role: under the hypotheses $tx-u\neq0$ on $\operatorname{tsupp} g$, and $g=0$ elsewhere.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean#L176-L229

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
universe uI uZ
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.polynomial_decay (l : ℕ) (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B) :
    ∀ (g : ℝ → ℂ), HasCompactSupport g → ContDiff ℝ ∞ g → ∀ k : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t u M : ℝ), 0 < M → |t| ≤ B*M →
      (∀ x ∈ tsupport g, c*M ≤ |t*x-u|) → M^(k+l)*‖osc g t u k‖ ≤ C := by sorry
