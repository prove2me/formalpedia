-- Prove2me | Theorems.Thm_GaussianMatrix_gaussian_concentration
-- name    : GaussianMatrix.gaussian_concentration
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:42:25.17183+00:00
-- url     : https://prove2.me/theorems/1d5cb0e7-db65-472d-b9b4-af588381c0c1
-- title:
--   Gaussian concentration for Lipschitz functions of a Gaussian matrix: $\mathbb P\{h(G)\ge\mathbb E h(G)+Lt\}\le e^{-t^2/2}$
-- statement:
--   Let $h:\mathbb R^{p\times m}\to\mathbb R$ be Lipschitz with respect to the Frobenius norm with constant $L>0$,
--   $$|h(X)-h(Y)|\le L\,\|X-Y\|_F\qquad\text{for all }X,Y,$$
--   and let $G\in\mathbb R^{p\times m}$ be a standard Gaussian matrix. Then $h(G)$ is integrable and, for every $t\ge0$,
--   $$\mathbb P\bigl\{h(G)\ \ge\ \mathbb E\,h(G)+L\,t\bigr\}\ \le\ e^{-t^2/2}.$$
--
--   This is the concentration-of-measure inequality in Gauss space (Tsirelson–Ibragimov–Sudakov; Vershynin Proposition 5.34, Halko–Martinsson–Tropp Proposition 10.3) for the standard Gaussian vector $\operatorname{vec}G\in\mathbb R^{pm}$. Applied to the $1$-Lipschitz functions $G\mapsto\sigma_{\max}(G)$, $G\mapsto\sigma_{\min}(G)$ and $G\mapsto\|SGT\|$ it upgrades the expectation bounds of Gordon's theorem into tail bounds.
--
--   **Formalization Note.** The source states the bound with $\ge$ and no sign condition on $L$ and $t$; the formal statement requires $L>0$ and $t\ge0$, since for $L=0$ (a constant $h$) or $t<0$ the event has probability $1$. Vectors in $\mathbb R^{n}$ are the case $m=1$.
-- source:
--   N. Halko, P.-G. Martinsson, J. A. Tropp, *Finding structure with randomness: probabilistic algorithms for constructing approximate matrix decompositions*, SIAM Review 53(2), 2011, https://arxiv.org/abs/0909.4061 (v2), §10.1 p. 56, Proposition 10.3 (Concentration for functions of a Gaussian matrix): $|h(X)-h(Y)|\le L\|X-Y\|_F$ implies $\mathbb P\{h(G)\ge\mathbb E h(G)+Lt\}\le e^{-t^2/2}$; also R. Vershynin, *Introduction to the non-asymptotic analysis of random matrices*, Chapter 5 of Compressed Sensing: Theory and Applications (Y. Eldar, G. Kutyniok, eds.), Cambridge University Press, 2012, https://arxiv.org/abs/1011.3027 (v7), §5.3.1 p. 21, Proposition 5.34 (Concentration in Gauss space).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem gaussian_concentration {p m : ℕ} (h : (Fin p → Fin m → ℝ) → ℝ) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ X Y, |h X - h Y| ≤ L * frobNorm (Matrix.of X - Matrix.of Y)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable h (gaussianMatrix p m) ∧
    (gaussianMatrix p m) {X | (∫ Y, h Y ∂(gaussianMatrix p m)) + L * t ≤ h X}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by sorry
end GaussianMatrix
