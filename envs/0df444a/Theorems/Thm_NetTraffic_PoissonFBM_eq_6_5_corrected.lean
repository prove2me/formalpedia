-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_eq_6_5_corrected
-- name    : NetTraffic.PoissonFBM.eq_6_5_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:39.100554+00:00
-- url     : https://prove2.me/theorems/0109606e-a5b8-45de-9360-b5f4e74a41fc
-- title:
--   (6.5) (corrected σ²), p. 57 — (A(T) − λμ_on T)/σ_T(1) →d N(0, 2/((α−1)(2−α)(3−α)))
-- statement:
--   Let $F_{\mathrm{on}}$ satisfy (2.8) with $1<\alpha<2$, let $\lambda=\lambda(T)>0$ be non-decreasing and satisfy the fast growth Condition 2, and for each $T$ consider the infinite source Poisson model with rate $\lambda(T)$, cumulative input $A$ and mean length $\mu_{\mathrm{on}}$. With $\sigma_T^2(1)=\lambda T^3\bar F_{\mathrm{on}}(T)$,
--   $$\frac{A(T)-\lambda\mu_{\mathrm{on}}T}{\sigma_T(1)}\xrightarrow{d}N(0,\sigma^2),\qquad \sigma^2=\frac{2}{(\alpha-1)(2-\alpha)(3-\alpha)},\qquad T\to\infty .$$
--
--   This is the one-dimensional case of Theorem 3. **Correction.** The paper prints $\sigma^2=\frac1{3-\alpha}\big[\frac\alpha{2-\alpha}+\frac2{\mu_{\mathrm{on}}}\big]$ (6.6). Its (6.4) omits the factor $\lambda m_2\sim\lambda m_3\sim\lambda\mu_{\mathrm{on}}$ in the variances of the $A_2$ and $A_3$ terms, which contribute $1/(3-\alpha)$ each, and (6.2) drops $(P_4-EP_4)T$, whose variance $T^2\lambda m_4\sim\lambda T^3\bar F_{\mathrm{on}}(T)/(\alpha-1)$ is of the same order under Condition 2. The sum $\frac\alpha{(2-\alpha)(3-\alpha)}+\frac2{3-\alpha}+\frac1{\alpha-1}$ is the value above, which also equals the limit of $\mathrm{Var}A(T)/\sigma_T^2(1)$ computed from (2.14).
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 57, (6.5) (limit variance corrected, see description)

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- (6.5), p. 57, with the corrected variance: under Condition 2,
`(A(T) - λμ_on T)/σ_T(1) →d N(0, σ²)` with `σ² = 2/((α-1)(2-α)(3-α))`. -/
theorem eq_6_5_corrected
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α)
    (lam : ℝ → ℝ) (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, NetTraffic.PoissonStable.IsPoissonModel (P T) (lam T) Fon (Γ T) (X T))
    (hC2 : Condition2 Fon lam) :
    TendstoInDistribution
      (fun T ω => (NetTraffic.PoissonStable.A (Γ T) (X T) T ω - lam T * NetTraffic.PoissonStable.muOn Fon * T) / Real.sqrt (sigmaT2 Fon lam T))
      atTop id P (gaussianReal 0 (sigma2 α).toNNReal) := by sorry

end NetTraffic.PoissonFBM
