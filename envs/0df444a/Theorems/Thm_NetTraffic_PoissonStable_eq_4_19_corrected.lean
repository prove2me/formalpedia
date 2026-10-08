-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_eq_4_19_corrected
-- name    : NetTraffic.PoissonStable.eq_4_19_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:22.465105+00:00
-- url     : https://prove2.me/theorems/0f717c3d-aa7d-4d7b-b13e-362383e4a1ea
-- title:
--   (4.19) (corrected), p. 38 — A₁₁/b(λT) →d S_α(C_α^{−1/α}, 1, 0)
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$; $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ is the quantile function (2.9); the connection rate $\lambda=\lambda(T)>0$ is a non-decreasing function of $T$ (§3.1), and $b(\lambda T)$ means $b$ evaluated at $\lambda(T)\,T$. Each $T$ carries its own probability space $(\Omega_T,P_T)$ with an infinite source Poisson model of rate $\lambda(T)$ and length law $F_{\mathrm{on}}$; the statement holds for every such family. Let $A_{11}=\sum_{k:(\Gamma_k,X_k)\in R_1}(X_k-Ej_1)$ in the $T$-th model, and $C_\alpha=(1-\alpha)/(\Gamma(2-\alpha)\cos(\pi\alpha/2))$.
--
--   If Condition 1 holds, there is a probability law $\nu$ on $\mathbb R$ with characteristic function that of $S_\alpha(C_\alpha^{-1/\alpha},1,0)$,
--   $$\int e^{i\theta x}\nu(dx)=\exp\{-C_\alpha^{-1}|\theta|^\alpha(1-i\,\mathrm{sign}(\theta)\tan(\pi\alpha/2))\},$$
--   and
--   $$\frac{A_{11}}{b(\lambda T)}\xrightarrow{d}\nu .$$
--
--   This is the core stable limit of the proof of Theorem 1.
--
--   **Correction.** The page prints the limit $X_{\alpha,1,1}(1)\sim S_\alpha(1,1,0)$. The tail limit $\lambda T\,P(j_1>b(\lambda T)x)\to x^{-\alpha}$ of pp. 37–38 identifies the Lévy measure $\alpha x^{-\alpha-1}dx$ on $(0,\infty)$; the totally skewed stable law with that Lévy measure has $\sigma^\alpha=\Gamma(1-\alpha)\cos(\pi\alpha/2)=C_\alpha^{-1}$, which is also the paper's own criterion on p. 47 with $c=1$. Since $C_\alpha\ne1$ on $(1,2)$, the printed scale is wrong and the scale $C_\alpha^{-1/\alpha}$ is stated.
--
--   **Formalization Note** $A_{11}$ is written $A_1-Ej_1P_1$; the existence of $\nu$ is part of the claim and the characteristic function pins it uniquely.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 38, (4.19) (limit scale corrected, see description)

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem eq_4_19_corrected
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC1 : Condition1 Fon lam)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, IsPoissonModel (P T) (lam T) Fon (Γ T) (X T)) :
    ∃ ν : ProbabilityMeasure ℝ,
      (∀ θ : ℝ, charFun (ν : Measure ℝ) θ = stableCharFun α (sigmaConst α) 1 0 θ) ∧
      TendstoInLaw P (fun T ω => A11 Fon (Γ T) (X T) T ω / b Fon (lam T * T)) ν := by sorry

end NetTraffic.PoissonStable
