-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_eq_4_17
-- name    : NetTraffic.PoissonStable.eq_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:26.610978+00:00
-- url     : https://prove2.me/theorems/bc495fe8-bec9-47bc-82aa-5f1bc829fb09
-- title:
--   (4.17), p. 37 — A₁₂ = O_P([λT]^{1/2}) = o_P(b(λT))
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$; $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ is the quantile function (2.9); the connection rate $\lambda=\lambda(T)>0$ is a non-decreasing function of $T$ (§3.1), and $b(\lambda T)$ means $b$ evaluated at $\lambda(T)\,T$. Each $T$ carries its own probability space $(\Omega_T,P_T)$ with an infinite source Poisson model of rate $\lambda(T)$ and length law $F_{\mathrm{on}}$; the statement holds for every such family. In the $T$-th model let $P_1$ be the number of points $(\Gamma_k,X_k)$ in $R_1$, $Ej_1$ the mean of the law (4.4), and $A_{12}=Ej_1\,(P_1-EP_1)$.
--
--   If Condition 1 holds, then $A_{12}=O_P([\lambda T]^{1/2})$, i.e. for every $\varepsilon>0$ there is $K$ with $P_T\big(|A_{12}|>K(\lambda T)^{1/2}\big)\le\varepsilon$ for all large $T$, and
--   $$\frac{A_{12}}{b(\lambda T)}\xrightarrow{P}0 .$$
--
--   The Poisson fluctuation of the number of complete transmissions is of order $(\lambda T)^{1/2}$ and thus negligible on the stable scale.
--
--   **Formalization Note** Both parts of (4.17) are stated: the $O_P([\lambda T]^{1/2})$ bound as tightness of $A_{12}/(\lambda T)^{1/2}$, and $o_P(b(\lambda T))$ as convergence in probability to $0$ of $A_{12}/b(\lambda T)$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 37, (4.17)

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem eq_4_17
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC1 : Condition1 Fon lam)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, IsPoissonModel (P T) (lam T) Fon (Γ T) (X T)) :
    (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ᶠ T in atTop,
      (P T).real {ω | K * Real.sqrt (lam T * T) < |A12 Fon (P T) (Γ T) (X T) T ω|} ≤ ε) ∧
    TendstoInProbZero P (fun T ω => A12 Fon (P T) (Γ T) (X T) T ω / b Fon (lam T * T)) := by sorry

end NetTraffic.PoissonStable
