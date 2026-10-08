-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_lemma_2_fast
-- name    : NetTraffic.PoissonFBM.lemma_2_fast
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:39.3041+00:00
-- url     : https://prove2.me/theorems/3f7fa198-4c9a-4ed8-a383-dc1cfcab4e73
-- title:
--   Lemma 2, fast part, p. 31 — under Condition 2, λT² F̄_on(T)/b(λT) → ∞
-- statement:
--   Let $F_{\mathrm{on}}$ satisfy (2.8) with $1<\alpha<2$, let $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ be the quantile function (2.9), and let $\lambda=\lambda(T)>0$ be non-decreasing. If the fast growth Condition 2 holds, $b(\lambda T)/T\to\infty$, then
--   $$\lim_{T\to\infty}\frac{\lambda T^2\,\bar F_{\mathrm{on}}(T)}{b(\lambda T)}=\infty .$$
--
--   This is the fast-growth half of Lemma 2, (3.4); the slow-growth half (limit $0$ under Condition 1) belongs to the companion mission.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 31, Lemma 2 (3.4), Condition 2 part

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- Lemma 2, fast part (p. 31): if Condition 2 holds, then `λT² F̄_on(T)/b(λT) → ∞`. -/
theorem lemma_2_fast
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α)
    (lam : ℝ → ℝ) (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC2 : Condition2 Fon lam) :
    Tendsto (fun T => lam T * T ^ 2 * NetTraffic.PoissonStable.Fbar Fon T / NetTraffic.PoissonStable.b Fon (lam T * T)) atTop atTop := by sorry

end NetTraffic.PoissonFBM
