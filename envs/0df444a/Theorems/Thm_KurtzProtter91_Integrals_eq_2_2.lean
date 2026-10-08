-- Prove2me | Theorems.Thm_KurtzProtter91_Integrals_eq_2_2
-- name    : KurtzProtter91.Integrals.eq_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:44.903727+00:00
-- url     : https://prove2.me/theorems/9fc45d90-4589-4f04-b26e-fc812ae6683f
-- title:
--   (2.2) — ∫xₙ(s−) dJ_δ(yₙ)(s) → ∫x(s−) dJ_δ(y)(s), jointly with (xₙ, yₙ)
-- statement:
--   Let $\delta\in(0,\infty]$, let $x_n,x$ be cadlag paths with values in the $k\times m$ real matrices and $y_n,y$ cadlag paths in $\mathbb R^m$, and suppose $(x_n,y_n)\to(x,y)$ in the Skorohod topology on $D_{\mathbb M^{km}\times\mathbb R^m}[0,\infty)$. Let $I_n=\int_0^\cdot x_n(s-)\,dJ_\delta(y_n)(s)$ and $I=\int_0^\cdot x(s-)\,dJ_\delta(y)(s)$ (left-point Riemann-sum limits (1.7)). Then
--   $$(x_n,y_n,I_n)\to(x,y,I)\quad\text{in the Skorohod topology on }D_{\mathbb M^{km}\times\mathbb R^m\times\mathbb R^k}[0,\infty);$$
--   in particular (2.2): $\int_0^\cdot x_n(s-)\,dJ_\delta(y_n)(s)\to\int_0^\cdot x(s-)\,dJ_\delta(y)(s)$.
--
--   In the proof of Theorem 2.2 this handles the large jumps $J_\delta(Y_n)$ of the integrator, which are removed before the martingale estimate.
--
--   **Formalization Note** The page writes (2.2) without fixing dimensions; the statement is for matrix-valued $x$ and vector-valued $y$, as the proof applies it to $(X_n,Y_n)$. It is stated jointly with $(x_n,y_n)$, the form the proof of Theorem 2.2 uses and which the page's appeal to (1.12) (whose parenthetical gives joint convergence) yields; the page's display is the third component. $J_\delta(y)$ is a step path, so the integrals are finite sums $\sum_{s\le t}x(s-)\Delta J_\delta(y)(s)$.
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1039, Section 2, (2.2)

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open Filter Topology
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

theorem eq_2_2 {k m : ℕ} (δ : ℝ≥0∞) (hδ : 0 < δ) (xs : ℕ → ℝ≥0 → Fin k → Fin m → ℝ)
    (ys : ℕ → ℝ≥0 → Fin m → ℝ) (x : ℝ≥0 → Fin k → Fin m → ℝ) (y : ℝ≥0 → Fin m → ℝ)
    (Is : ℕ → ℝ≥0 → Fin k → ℝ) (I : ℝ≥0 → Fin k → ℝ)
    (hconv : SkorohodTendsto (fun n t => (xs n t, ys n t)) (fun t => (x t, y t)))
    (hIs : ∀ n, HasLeftIntegral (xs n) (Jdelta δ (ys n)) (Is n))
    (hI : HasLeftIntegral x (Jdelta δ y) I) :
    SkorohodTendsto (fun n t => (xs n t, ys n t, Is n t)) (fun t => (x t, y t, I t)) := by sorry

end KurtzProtter91.Integrals
