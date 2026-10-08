-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Ergodicity_lemma_11
-- name    : JSQHalfinWhitt.Ergodicity.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:40:35.924563+00:00
-- url     : https://prove2.me/theorems/cea06a81-5c7d-4a95-aff2-9a194f9097e4
-- title:
--   Lemma 11 — f^{(1)} : Ω → ℝ₊ belongs to C²(Ω), with explicit first partials
-- statement:
--   Fix an integer $n\ge1$ and $0<\beta<\kappa_1<\kappa_2$, let $\phi=\phi^{(\kappa_1/\sqrt n,\kappa_2/\sqrt n)}$ and write $g(x,t)=\beta/\sqrt n-(x_1+\beta/\sqrt n)e^{-t}-x_2te^{-t}$. Let $f^{(1)}$ be the function
--   $$f^{(1)}(x)=\begin{cases}\tilde\tau^{(\kappa_2)}(x)+\int_{\tilde\tau^{(\kappa_2)}(x)}^{\tilde\tau^{(\kappa_1)}(x)}\phi(g(x,t))\,dt,& x_1\le-\kappa_2/\sqrt n,\\ \int_0^{\tilde\tau^{(\kappa_1)}(x)}\phi(g(x,t))\,dt,& x_1\in[-\kappa_2/\sqrt n,-\kappa_1/\sqrt n],\\ 0,& x_1\in[-\kappa_1/\sqrt n,0].\end{cases}$$
--   Then $f^{(1)}\ge0$ on $\Omega$, $f^{(1)}\in C^2(\Omega)$, and on each of the three closed regions
--   $$f^{(1)}_1(x)=-\int e^{-t}\phi'(g(x,t))\,dt,\qquad f^{(1)}_2(x)=-\int te^{-t}\phi'(g(x,t))\,dt,$$
--   with the integral over $[\tilde\tau^{(\kappa_2)}(x),\tilde\tau^{(\kappa_1)}(x)]$ when $x_1\le-\kappa_2/\sqrt n$ and over $[0,\tilde\tau^{(\kappa_1)}(x)]$ when $x_1\in[-\kappa_2/\sqrt n,-\kappa_1/\sqrt n]$, while $f^{(1)}_1=f^{(1)}_2=0$ when $x_1\in[-\kappa_1/\sqrt n,0]$.
--
--   $f^{(1)}$ is the solution of the first PDE (5.9) used in Lemma 8; the derivative formulas give the bounds (5.15) and the reflection condition on $\{x_1=0\}$.
--
--   **Formalization Note** The partials are the one-sided partials on $\Omega$ (derivatives within $\Omega$), $\phi'$ is `deriv φ`, and the integrals are oriented interval integrals as printed. The derivative formulas are asserted on each closed region, so on a shared boundary line both printed formulas hold. "$f^{(1)}:\Omega\to\mathbb R_+$" is the nonnegativity clause.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 36, Lemma 11; standing assumptions κ_1 < κ_2, κ_1 > β, φ = φ^{(κ_1/√n, κ_2/√n)} on p. 35

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Ergodicity_Candidates

namespace JSQHalfinWhitt.Ergodicity

/-- Lemma 11, p. 36. Let `n ≥ 1`, `0 < β < κ₁ < κ₂` and `φ = φ^{(κ₁/√n, κ₂/√n)}`. The function
`f^{(1)}` (`f1`) is nonnegative on `Ω`, belongs to `C²(Ω)`, and its partial derivatives on `Ω` are, on
each closed region of its definition,
`f^{(1)}₁ = −∫ e^{−t} φ'(β/√n − (x₁+β/√n)e^{−t} − x₂te^{−t}) dt`,
`f^{(1)}₂ = −∫ t e^{−t} φ'(β/√n − (x₁+β/√n)e^{−t} − x₂te^{−t}) dt`,
the integral running over `[τ̃^{(κ₂)}(x), τ̃^{(κ₁)}(x)]` when `x₁ ≤ −κ₂/√n` and over `[0, τ̃^{(κ₁)}(x)]`
when `x₁ ∈ [−κ₂/√n, −κ₁/√n]`, and both derivatives vanish when `x₁ ∈ [−κ₁/√n, 0]`. -/
theorem lemma_11 (n : ℕ) (hn : 0 < n) (β κ1 κ2 : ℝ) (hβ : 0 < β) (hκ1 : β < κ1)
    (hκ12 : κ1 < κ2) :
    (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, 0 ≤ f1 n β κ1 κ2 x) ∧ ContDiffOn ℝ 2 (f1 n β κ1 κ2) JSQHalfinWhitt.Tightness.Omega ∧
    (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, x.1 ≤ -κ2 / Real.sqrt n →
      d1 (f1 n β κ1 κ2) x = -∫ t in tauTilde n β κ2 x..tauTilde n β κ1 x,
        Real.exp (-t) * deriv (phiK n κ1 κ2) (fluidArg n β x t)) ∧
    (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, -κ2 / Real.sqrt n ≤ x.1 → x.1 ≤ -κ1 / Real.sqrt n →
      d1 (f1 n β κ1 κ2) x = -∫ t in (0 : ℝ)..tauTilde n β κ1 x,
        Real.exp (-t) * deriv (phiK n κ1 κ2) (fluidArg n β x t)) ∧
    (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, -κ1 / Real.sqrt n ≤ x.1 → d1 (f1 n β κ1 κ2) x = 0) ∧
    (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, x.1 ≤ -κ2 / Real.sqrt n →
      d2 (f1 n β κ1 κ2) x = -∫ t in tauTilde n β κ2 x..tauTilde n β κ1 x,
        t * Real.exp (-t) * deriv (phiK n κ1 κ2) (fluidArg n β x t)) ∧
    (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, -κ2 / Real.sqrt n ≤ x.1 → x.1 ≤ -κ1 / Real.sqrt n →
      d2 (f1 n β κ1 κ2) x = -∫ t in (0 : ℝ)..tauTilde n β κ1 x,
        t * Real.exp (-t) * deriv (phiK n κ1 κ2) (fluidArg n β x t)) ∧
    (∀ x ∈ JSQHalfinWhitt.Tightness.Omega, -κ1 / Real.sqrt n ≤ x.1 → d2 (f1 n β κ1 κ2) x = 0) := by sorry

end JSQHalfinWhitt.Ergodicity
