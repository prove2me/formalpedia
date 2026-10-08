-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_eq_4_21
-- name    : NetTraffic.PoissonStable.eq_4_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:10.960896+00:00
-- url     : https://prove2.me/theorems/e1a9a1b4-cef7-4e6d-a7af-365c93267963
-- title:
--   (4.20)–(4.21), p. 38 — A₁₃ = EA₁ − λμ_on T ∼ −(const)λT²F̄_on(T) = o(b(λT))
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$; $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ is the quantile function (2.9); the connection rate $\lambda=\lambda(T)>0$ is a non-decreasing function of $T$ (§3.1), and $b(\lambda T)$ means $b$ evaluated at $\lambda(T)\,T$. Each $T$ carries its own probability space $(\Omega_T,P_T)$ with an infinite source Poisson model of rate $\lambda(T)$ and length law $F_{\mathrm{on}}$; the statement holds for every such family. Let $A_{13}=E A_1-\lambda\mu_{\mathrm{on}}T$, a deterministic number, with $A_1=\sum_k X_k\mathbf 1[(\Gamma_k,X_k)\in R_1]$.
--
--   If Condition 1 holds, then
--   $$\frac{A_{13}}{b(\lambda T)}\to0,$$
--   and there is a constant $c>0$ with
--   $$\frac{A_{13}}{\lambda T^2\,\bar F_{\mathrm{on}}(T)}\to-c .$$
--
--   The centring error of $A_1$ is of order $\lambda T^2\bar F_{\mathrm{on}}(T)$, negligible by Lemma 2.
--
--   **Formalization Note** The page's "(const)" is an existentially quantified $c>0$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 38, (4.20)–(4.21)

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem eq_4_21
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC1 : Condition1 Fon lam)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, IsPoissonModel (P T) (lam T) Fon (Γ T) (X T)) :
    Tendsto (fun T => A13 Fon (lam T) (P T) (Γ T) (X T) T / b Fon (lam T * T)) atTop (𝓝 0) ∧
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun T => A13 Fon (lam T) (P T) (Γ T) (X T) T / (lam T * T ^ 2 * Fbar Fon T))
        atTop (𝓝 (-c)) := by sorry

end NetTraffic.PoissonStable
