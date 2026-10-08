-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_increment_fourth_moment
-- name    : NetTraffic.PoissonFBM.increment_fourth_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:38.459867+00:00
-- url     : https://prove2.me/theorems/bc73ecca-01ee-424a-a490-f69e79846cb0
-- title:
--   §6.3, p. 61 — E(G_T(t+u) − G_T(t))⁴ = E G_T(u)⁴ ≤ cu² for 0 ≤ t+u ≤ K
-- statement:
--   Let $F_{\mathrm{on}}$ satisfy (2.8) with $1<\alpha<2$, let $\lambda=\lambda(T)>0$ be non-decreasing and satisfy the fast growth Condition 2, and for each $T$ let $G_T$ be the normalised input process of the infinite source Poisson model with rate $\lambda(T)$. Then for every $K>0$ there are a constant $c$ and $T_0$ such that for all $T\ge T_0$ and all $t,u\ge0$ with $t+u\le K$, the fourth power of the increment is integrable and
--   $$E\big(G_T(t+u)-G_T(t)\big)^4=E\,G_T(u)^4\le c\,u^2 .$$
--
--   By the moment criterion for tightness (Billingsley, Theorem 12.3) this bound makes $\{G_T\}$ tight in the $J_1$ topology on $\mathbb D[0,K]$ for every $K$, the second half of the proof of Theorem 3.
--
--   **Formalization Note** $c$ is one constant for all $T\ge T_0$ and all admissible $t,u$, chosen after $K$; it absorbs the factor $\sigma^{-4}$ of the normalisation, so the bound does not depend on the value of $\sigma^2$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 61, §6.3, display after "Since A_T has stationary increments"

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- §6.3, p. 61: under Condition 2, for every `K > 0` there are a constant `c` and `T₀` such that
for all `T ≥ T₀` and `t, u ≥ 0` with `t + u ≤ K`,
`E(G_T(t + u) - G_T(t))⁴ = E G_T(u)⁴ ≤ c u²` (the fourth power being integrable). -/
theorem increment_fourth_moment
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α)
    (lam : ℝ → ℝ) (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, NetTraffic.PoissonStable.IsPoissonModel (P T) (lam T) Fon (Γ T) (X T))
    (hC2 : Condition2 Fon lam) :
    ∀ K : ℝ≥0, 0 < K → ∃ c T₀ : ℝ, ∀ T ≥ T₀, ∀ t u : ℝ≥0, t + u ≤ K →
      Integrable (fun ω => (G Fon α lam (Γ T) (X T) T (t + u) ω -
        G Fon α lam (Γ T) (X T) T t ω) ^ 4) (P T) ∧
      ∫ ω, (G Fon α lam (Γ T) (X T) T (t + u) ω - G Fon α lam (Γ T) (X T) T t ω) ^ 4 ∂(P T) =
        ∫ ω, (G Fon α lam (Γ T) (X T) T u ω) ^ 4 ∂(P T) ∧
      ∫ ω, (G Fon α lam (Γ T) (X T) T (t + u) ω - G Fon α lam (Γ T) (X T) T t ω) ^ 4 ∂(P T) ≤
        c * (u : ℝ) ^ 2 := by sorry

end NetTraffic.PoissonFBM
