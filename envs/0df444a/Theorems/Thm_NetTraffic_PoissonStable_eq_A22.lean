-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_eq_A22
-- name    : NetTraffic.PoissonStable.eq_A22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:26.96967+00:00
-- url     : https://prove2.me/theorems/9d4851dc-8cd5-4563-9f5e-cef42189cf61
-- title:
--   §4.5, p. 39 — EA₂₂ = o(b(λT)) and A₂₂/b(λT) → 0 in probability
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$; $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ is the quantile function (2.9); the connection rate $\lambda=\lambda(T)>0$ is a non-decreasing function of $T$ (§3.1), and $b(\lambda T)$ means $b$ evaluated at $\lambda(T)\,T$. Each $T$ carries its own probability space $(\Omega_T,P_T)$ with an infinite source Poisson model of rate $\lambda(T)$ and length law $F_{\mathrm{on}}$; the statement holds for every such family. For $0<t_1<t_2$ let
--   $$A_{22}=\sum_{0<\Gamma_k\le Tt_1}X_k\,\mathbf 1[Tt_1<\Gamma_k+X_k\le Tt_2]$$
--   in the $T$-th model, the input of transmissions started in $(0,Tt_1]$ and finished in $(Tt_1,Tt_2]$.
--
--   If Condition 1 holds, then
--   $$\frac{EA_{22}}{b(\lambda T)}\to0\qquad\text{and}\qquad\frac{A_{22}}{b(\lambda T)}\xrightarrow{P}0 .$$
--
--   This is the step that reduces the convergence of the two-dimensional distributions to the one-dimensional limit.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 39, §4.5, display "EA₂₂ = … = o(b(λT))"

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem eq_A22
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC1 : Condition1 Fon lam)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, IsPoissonModel (P T) (lam T) Fon (Γ T) (X T)) :
    ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ < t₂ →
      Tendsto (fun T => (∫ ω, A22 (Γ T) (X T) (T * t₁) (T * t₂) ω ∂(P T)) / b Fon (lam T * T))
        atTop (𝓝 0) ∧
      TendstoInProbZero P (fun T ω => A22 (Γ T) (X T) (T * t₁) (T * t₂) ω / b Fon (lam T * T)) := by sorry

end NetTraffic.PoissonStable
