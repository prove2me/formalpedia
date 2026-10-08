-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_one_dim_corrected
-- name    : NetTraffic.PoissonStable.one_dim_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:18.827988+00:00
-- url     : https://prove2.me/theorems/a70785cc-335d-4cb7-9227-c5409999e48a
-- title:
--   §4.4, p. 38 (corrected) — (A(T) − λμ_on T)/b(λT) →d S_α(C_α^{−1/α}, 1, 0)
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$; $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ is the quantile function (2.9); the connection rate $\lambda=\lambda(T)>0$ is a non-decreasing function of $T$ (§3.1), and $b(\lambda T)$ means $b$ evaluated at $\lambda(T)\,T$. Each $T$ carries its own probability space $(\Omega_T,P_T)$ with an infinite source Poisson model of rate $\lambda(T)$ and length law $F_{\mathrm{on}}$; the statement holds for every such family. Let $C_\alpha=(1-\alpha)/(\Gamma(2-\alpha)\cos(\pi\alpha/2))$.
--
--   If Condition 1 holds, there is a probability law $\nu$ on $\mathbb R$, the law $S_\alpha(C_\alpha^{-1/\alpha},1,0)$ identified by its characteristic function
--   $$\int e^{i\theta x}\nu(dx)=\exp\{-C_\alpha^{-1}|\theta|^\alpha(1-i\,\mathrm{sign}(\theta)\tan(\pi\alpha/2))\},$$
--   such that
--   $$\frac{A(T)-\lambda\mu_{\mathrm{on}}T}{b(\lambda T)}\xrightarrow{d}\nu .$$
--
--   This is the one-dimensional case $t=1$ of Theorem 1.
--
--   **Correction.** The page concludes that "$A(T)$ has the desired α-stable limit", i.e. $X_{\alpha,1,1}(1)\sim S_\alpha(1,1,0)$. As explained for (4.19), the limit has scale $C_\alpha^{-1/\alpha}$, not $1$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 38, end of §4.4 (limit scale corrected, see description)

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem one_dim_corrected
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC1 : Condition1 Fon lam)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, IsPoissonModel (P T) (lam T) Fon (Γ T) (X T)) :
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ θ : ℝ, charFun (ν : Measure ℝ) θ = stableCharFun α (sigmaConst α) 1 0 θ) ∧
      TendstoInLaw P (fun T ω =>
        (A (Γ T) (X T) T ω - lam T * muOn Fon * T) / b Fon (lam T * T)) ν := by sorry

end NetTraffic.PoissonStable
