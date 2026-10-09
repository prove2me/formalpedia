-- Prove2me | Theorems.Thm_LookbackMOT_HL_eq_3_23
-- name    : LookbackMOT.HL.eq_3_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:53.998995+00:00
-- url     : https://prove2.me/theorems/0d216bbd-8e46-4507-8073-37c19ddcf415
-- title:
--   (3.23), p. 14 — Neumann condition on the diagonal: v^ψ_m(m, m) = 0 for all m
-- statement:
--   Let $g:\mathbb R\to\mathbb R_+$ be $C^1$ and nondecreasing, let $\lambda:\mathbb R\to\mathbb R$ be convex with right derivative $\lambda'$ and second-derivative measure $\lambda''$, and let $\psi\in\Psi^\lambda$: $\psi$ is right-continuous, $\psi(m)<m$ for all $m$, and $\psi$ solves the weak ODE (3.21). Let
--   $$v^\psi(x,m)=g(m)-\lambda(x\wedge\psi(m))-\lambda'(\psi(m))\,(x-x\wedge\psi(m)),\qquad x\le m,$$
--   be Peskir's candidate value function (3.18). Then $v^\psi$ is differentiable in $m$ on the diagonal, with
--   $$v^\psi_m(m,m)=0\qquad\text{for all }m\in\mathbb R .$$
--
--   This is the Neumann (reflection) condition of the dynamic programming equation (3.17); it is what makes the $dM_t$ term vanish in the Itô–Tanaka expansion of $v^\psi(X_t,M_t)$ in the proof of Lemma 3.1.
--
--   **Formalization Note** $v^\psi$ is defined on $\Delta=\{x\le m\}$, so the derivative in $m$ at the diagonal point $(m,m)$ is the right derivative: the statement is that $m'\mapsto v^\psi(m,m')$ has derivative $0$ at $m'=m$ within $[m,\infty)$. Of the hypothesis $\lambda\in\hat\Lambda^\mu_0$ of Lemma 3.1 only convexity is used here, so only convexity is assumed. The weak ODE is in the form fixed in the Setting file.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 14, (3.23), step (1) of the proof of Lemma 3.1

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem eq_3_23 (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (lam : ℝ → ℝ) (hlam : ConvexOn ℝ Set.univ lam)
    (ν₂ : Measure ℝ) (hν₂ : IsSecondDerivMeasure lam ν₂) (ψ : ℝ → ℝ) (hψ : InPsi g lam ν₂ ψ) :
    ∀ m : ℝ, HasDerivWithinAt (fun m' => vpsi g lam ψ m m') 0 (Set.Ici m) m := by sorry

end LookbackMOT.HL
