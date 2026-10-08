-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_eq_6_8
-- name    : NetTraffic.PoissonFBM.eq_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:42.120055+00:00
-- url     : https://prove2.me/theorems/581b5f8e-cc2c-4369-b82c-feaed2081528
-- title:
--   (6.8), p. 59 — E(A₁ − EA₁)⁴/σ_T⁴(1) ≤ cu² for A₁ built from U = uT, 0 ≤ u ≤ K
-- statement:
--   Let $F_{\mathrm{on}}$ satisfy (2.8) with $1<\alpha<2$, let $\lambda=\lambda(T)>0$ be non-decreasing and satisfy the fast growth Condition 2, and for each $T$ consider the infinite source Poisson model with rate $\lambda(T)$. For a horizon $U$ let $A_1(U)=\sum_kX_k\mathbf 1[(\Gamma_k,X_k)\in R_1(U)]$ with $R_1(U)=\{(s,y):0<s\le U,\ y>0,\ s+y\le U\}$. Then for every $K>0$ there are a constant $c$ and $T_0$ such that for all $T\ge T_0$ and all $0\le u\le K$, with $U=uT$, the fourth power of $A_1(U)-EA_1(U)$ is integrable and
--   $$\frac{E\big(A_1(U)-EA_1(U)\big)^4}{\sigma_T^4(1)}\le c\,u^2,\qquad \sigma_T^2(1)=\lambda T^3\bar F_{\mathrm{on}}(T).$$
--
--   This is the first of the four fourth-moment bounds that give tightness of $G_T$ in $\mathbb D[0,K]$.
--
--   **Formalization Note** The page's $c$ is a "generic constant"; it is stated as one constant for all $T\ge T_0$ and $u\in[0,K]$, chosen after $K$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 59, (6.7)–(6.8)

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- (6.8), p. 59: under Condition 2, for every `K > 0` there are a constant `c` and `T₀` such that
for all `T ≥ T₀` and `0 ≤ u ≤ K`, with `A_1 = A_1(U)` built from the horizon `U = uT`,
`E(A_1 - EA_1)⁴/σ_T⁴(1) ≤ c u²` (the fourth power being integrable). -/
theorem eq_6_8
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α)
    (lam : ℝ → ℝ) (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, NetTraffic.PoissonStable.IsPoissonModel (P T) (lam T) Fon (Γ T) (X T))
    (hC2 : Condition2 Fon lam) :
    ∀ K : ℝ, 0 < K → ∃ c T₀ : ℝ, ∀ T ≥ T₀, ∀ u ∈ Set.Icc (0 : ℝ) K,
      Integrable (fun ω => (NetTraffic.PoissonStable.A1 (Γ T) (X T) (u * T) ω -
        ∫ ω', NetTraffic.PoissonStable.A1 (Γ T) (X T) (u * T) ω' ∂(P T)) ^ 4) (P T) ∧
      (∫ ω, (NetTraffic.PoissonStable.A1 (Γ T) (X T) (u * T) ω - ∫ ω', NetTraffic.PoissonStable.A1 (Γ T) (X T) (u * T) ω' ∂(P T)) ^ 4 ∂(P T)) /
          (sigmaT2 Fon lam T) ^ 2 ≤ c * u ^ 2 := by sorry

end NetTraffic.PoissonFBM
