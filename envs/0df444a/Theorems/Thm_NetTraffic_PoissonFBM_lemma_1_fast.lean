-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_lemma_1_fast
-- name    : NetTraffic.PoissonFBM.lemma_1_fast
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:47.135998+00:00
-- url     : https://prove2.me/theorems/339af6e7-4f59-43bf-8239-6429bae24c67
-- title:
--   Lemma 1, part 2, p. 30 — Condition 2 ⇔ λT F̄_on(T) → ∞ ⇔ Cov(N_T(0), N_T(T)) → ∞
-- statement:
--   Let $F_{\mathrm{on}}$ satisfy (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying. Let $\lambda=\lambda(T)>0$ be non-decreasing in $T$, and for each $T$ let $N_T$ be the number of active sources of the infinite source Poisson model with rate $\lambda(T)$ and length law $F_{\mathrm{on}}$. Then the following three conditions are equivalent:
--   1. the fast growth Condition 2, $b(\lambda T)/T\to\infty$;
--   2. $$\lim_{T\to\infty}\lambda T\,\bar F_{\mathrm{on}}(T)=\infty;$$
--   3. $$\lim_{T\to\infty}\mathrm{Cov}\big(N_T(0),N_T(T)\big)=\infty .$$
--
--   The lemma translates the growth condition on the quantile function $b$ into the number of long transmissions that straddle a window of length $T$, and into the correlation of the input rate at lag $T$.
--
--   **Formalization Note** The Poisson model is stationary by construction, so "the stationary version of $N_T$" adds no hypothesis.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 30, Lemma 1, part 2

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- Lemma 1, part 2 (p. 30): under (2.8), the fast growth Condition 2 is equivalent to
`λT F̄_on(T) → ∞`, and to `Cov(N_T(0), N_T(T)) → ∞`. -/
theorem lemma_1_fast
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α)
    (lam : ℝ → ℝ) (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, NetTraffic.PoissonStable.IsPoissonModel (P T) (lam T) Fon (Γ T) (X T)) :
    (Condition2 Fon lam ↔ Tendsto (fun T => lam T * T * NetTraffic.PoissonStable.Fbar Fon T) atTop atTop) ∧
    (Condition2 Fon lam ↔
      Tendsto (fun T => cov[fun ω => (NetTraffic.PoissonStable.N (Γ T) (X T) 0 ω : ℝ), fun ω => (NetTraffic.PoissonStable.N (Γ T) (X T) T ω : ℝ);
        P T]) atTop atTop) := by sorry

end NetTraffic.PoissonFBM
