-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_lemma_1_slow
-- name    : NetTraffic.PoissonStable.lemma_1_slow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:11.501646+00:00
-- url     : https://prove2.me/theorems/cbde149e-ca5f-4768-8cbf-05054cda5ae0
-- title:
--   Lemma 1, part 1, p. 30 — Condition 1 ⇔ λT F̄_on(T) → 0 ⇔ Cov(N_T(0), N_T(T)) → 0
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$; $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ is the quantile function (2.9); the connection rate $\lambda=\lambda(T)>0$ is a non-decreasing function of $T$ (§3.1), and $b(\lambda T)$ means $b$ evaluated at $\lambda(T)\,T$. Each $T$ carries its own probability space $(\Omega_T,P_T)$ with an infinite source Poisson model of rate $\lambda(T)$ and length law $F_{\mathrm{on}}$; the statement holds for every such family.
--
--   Then the slow growth condition 1, $b(\lambda T)/T\to0$, is equivalent to each of
--   $$\lim_{T\to\infty}\lambda T\,\bar F_{\mathrm{on}}(T)=0\qquad\text{and}\qquad\lim_{T\to\infty}\mathrm{Cov}(N_T(0),N_T(T))=0 .$$
--
--   The lemma restates the growth condition through the tail and through the dependence of the input rate at lag $T$: slow growth means that the dependence vanishes on the time scale $T$.
--
--   **Formalization Note** The page says "consider the stationary version of the input rate"; the two-sided Poisson model is stationary by construction, so no hypothesis is added.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 30, Lemma 1, part 1

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_1_slow
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, IsPoissonModel (P T) (lam T) Fon (Γ T) (X T)) :
    (Condition1 Fon lam ↔ Tendsto (fun T => lam T * T * Fbar Fon T) atTop (𝓝 0)) ∧
    (Condition1 Fon lam ↔ Tendsto (fun T =>
      cov[fun ω => (N (Γ T) (X T) 0 ω : ℝ), fun ω => (N (Γ T) (X T) T ω : ℝ); P T])
        atTop (𝓝 0)) := by sorry

end NetTraffic.PoissonStable
