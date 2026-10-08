-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_eq_4_15
-- name    : NetTraffic.PoissonStable.eq_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:11.889823+00:00
-- url     : https://prove2.me/theorems/f4786635-5e46-42bd-85fd-c9d316a2a9ea
-- title:
--   (4.15), p. 37 — A_i/b(λT) → 0 in probability, i = 2, 3, 4
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$; $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ is the quantile function (2.9); the connection rate $\lambda=\lambda(T)>0$ is a non-decreasing function of $T$ (§3.1), and $b(\lambda T)$ means $b$ evaluated at $\lambda(T)\,T$. Each $T$ carries its own probability space $(\Omega_T,P_T)$ with an infinite source Poisson model of rate $\lambda(T)$ and length law $F_{\mathrm{on}}$; the statement holds for every such family. Let $A_2,A_3,A_4$ be the pieces (4.2) of $A(T)$ in the $T$-th model, belonging to the regions $R_2,R_3,R_4$ of (4.1).
--
--   If Condition 1 holds, then
--   $$\frac{A_i}{b(\lambda T)}\xrightarrow{P}0,\qquad i=2,3,4 .$$
--
--   The transmissions that straddle $0$ or $T$ are asymptotically negligible; the stable limit comes from the transmissions inside $(0,T]$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 37, (4.15)

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem eq_4_15
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC1 : Condition1 Fon lam)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, IsPoissonModel (P T) (lam T) Fon (Γ T) (X T)) :
    TendstoInProbZero P (fun T ω => A2 (Γ T) (X T) T ω / b Fon (lam T * T)) ∧
    TendstoInProbZero P (fun T ω => A3 (Γ T) (X T) T ω / b Fon (lam T * T)) ∧
    TendstoInProbZero P (fun T ω => A4 (Γ T) (X T) T ω / b Fon (lam T * T)) := by sorry

end NetTraffic.PoissonStable
