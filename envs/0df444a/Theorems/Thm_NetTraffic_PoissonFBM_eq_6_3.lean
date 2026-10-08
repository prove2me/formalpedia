-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_eq_6_3
-- name    : NetTraffic.PoissonFBM.eq_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:58.050499+00:00
-- url     : https://prove2.me/theorems/739f313e-4b7c-46af-ad09-c9abff372fb7
-- title:
--   (6.3), p. 57 — under Condition 2, (A₁ − P₁Ej₁)/σ_T(1) →d N(0, σ₁²)
-- statement:
--   Let $F_{\mathrm{on}}$ satisfy (2.8) with $1<\alpha<2$, let $\lambda=\lambda(T)>0$ be non-decreasing and satisfy the fast growth Condition 2, and for each $T$ consider the infinite source Poisson model with rate $\lambda(T)$. With $A_1=\sum_kX_k\mathbf 1[(\Gamma_k,X_k)\in R_1]$, $P_1=\#\{k:(\Gamma_k,X_k)\in R_1\}$, $Ej_1$ the mean of the law (4.4), and $\sigma_T^2(1)=\lambda T^3\bar F_{\mathrm{on}}(T)$,
--   $$\frac{A_1-P_1\,Ej_1}{\sigma_T(1)}\xrightarrow{d}N(0,\sigma_1^2),\qquad \sigma_1^2=\frac{\alpha}{(2-\alpha)(3-\alpha)},\qquad T\to\infty .$$
--
--   $A_1-P_1Ej_1=\sum_k(X_k-Ej_1)\mathbf 1[(\Gamma_k,X_k)\in R_1]$ is the centred input of the transmissions that start and end in $(0,T]$; this is the first Gaussian component of the limit.
--
--   **Formalization Note** Convergence in distribution is Mathlib's `TendstoInDistribution` along $T\to\infty$ in $\mathbb R$, the limit being the identity on $(\mathbb R,N(0,\sigma_1^2))$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 57, (6.3)

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- (6.3), p. 57: under Condition 2, `(A_1 - P_1 E j_1)/σ_T(1) →d N(0, σ_1²)`, with
`σ_T²(1) = λT³F̄_on(T)` and `σ_1² = α/((2-α)(3-α))`. -/
theorem eq_6_3
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α)
    (lam : ℝ → ℝ) (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, NetTraffic.PoissonStable.IsPoissonModel (P T) (lam T) Fon (Γ T) (X T))
    (hC2 : Condition2 Fon lam) :
    TendstoInDistribution
      (fun T ω => (NetTraffic.PoissonStable.A1 (Γ T) (X T) T ω - (NetTraffic.PoissonStable.P1 (Γ T) (X T) T ω : ℝ) * NetTraffic.PoissonStable.Ej1 Fon T) /
        Real.sqrt (sigmaT2 Fon lam T))
      atTop id P (gaussianReal 0 (sigma1sq α).toNNReal) := by sorry

end NetTraffic.PoissonFBM
