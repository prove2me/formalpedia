-- Prove2me | Theorems.Thm_LookbackMOT_HL_lemma_3_2
-- name    : LookbackMOT.HL.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:18.910984+00:00
-- url     : https://prove2.me/theorems/8d7c3a7c-6cfd-4956-b0e8-d85e3ba89675
-- title:
--   Lemma 3.2, p. 15 — μ(λ) + u^λ(X₀, X₀) ≤ g(X₀) + ∫ φ(ψ(m), m) g′(m) dm for λ ∈ Λ̂^μ_0, ψ ∈ Ψ^λ
-- statement:
--   In the setting of Lemma 3.1, let $\lambda\in\hat\Lambda^\mu_0$ and $\psi\in\Psi^\lambda$, and let
--   $$\varphi(x,m)=\frac{c(x)-c_0(x)\mathbf 1_{m<X_0}}{m-x},\qquad c(x)=\int(\xi-x)^+\mu(d\xi),\quad c_0(x)=(X_0-x)^+ .$$
--   Then
--   $$\mu(\lambda)+u^\lambda(X_0,X_0)\ \le\ g(X_0)+\int_{\mathbb R}\varphi(\psi(m),m)\,g'(m)\,dm .$$
--
--   The right side depends on $\lambda$ only through $\psi$, so the dual problem (3.7) is bounded by a minimization over free boundaries that can be carried out pointwise in $m$; this is the route to the upper bound of Lemma 3.3.
--
--   **Formalization Note** The integrand is nonnegative ($\psi(m)<m$ and $c\ge c_0\ge c_0\mathbf 1_{m<X_0}$), so the integral is a $[0,\infty]$-valued integral over all of $\mathbb R$; the paper's remark that "the endpoints can be taken to $0$ and $\infty$" is the case $\mu([0,\infty))=1$ of the same nonnegativity and is not encoded. Both sides are in the extended reals. $g'$ is the derivative of the $C^1$ function $g$.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 15, Lemma 3.2 (with (3.25))

import Mathlib
import Definitions.Def_LookbackMOT_HL_Setting

open MeasureTheory ProbabilityTheory LookbackMOT.HL
open scoped NNReal ENNReal

namespace LookbackMOT.HL

theorem lemma_3_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ) (hB : IsFBrownian P ℱ B)
    (X₀ : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ1 : Integrable id μ)
    (hmean : ∫ x, x ∂μ = X₀)
    (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgC1 : ContDiff ℝ 1 g) (hgmono : Monotone g)
    (lam : ℝ → ℝ) (hlam : InLambda0Hat P ℱ B X₀ μ lam)
    (ν₂ : Measure ℝ) (hν₂ : IsSecondDerivMeasure lam ν₂) (ψ : ℝ → ℝ) (hψ : InPsi g lam ν₂ ψ) :
    ((∫ x, lam x ∂μ : ℝ) : EReal) + stopValue P ℱ B g lam X₀ X₀ ≤
      ((g X₀ : ℝ) : EReal) +
        ((∫⁻ m, ENNReal.ofReal (phi μ X₀ (ψ m) m * deriv g m) : ℝ≥0∞) : EReal) := by sorry

end LookbackMOT.HL
