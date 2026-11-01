-- Prove2me | Theorems.Thm_OnlineWass_lemma_1
-- name    : OnlineWass.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:30.850367+00:00
-- url     : https://prove2.me/theorems/c0ddb4f2-43ef-4af5-95d0-ec60cf3d6a34
-- title:
--   Lemma 1 — $R^{UB}_T\ge\mathbb E[R^*_T]$
-- statement:
--   Under Assumption 1 with $\rho$ of (2) as the distance of $\Theta$, for $c\ge0$ and independent $\theta_t\sim\mathcal P_t$,
--
--   $$
--   R^{UB}_T\ge\mathbb E[R^*_T].
--   $$
--
--   The fluid problem (4) is the standard deterministic upper bound on the offline optimum, and this comparison is the reason for introducing it.
--
--   **Formalization Note** The hypothesis $f(0;\theta)\ge0$ of the correction is not needed here.
--
--   Differences from the source:
--   - generalization: Θ ⊂ ℝˡ → Θ any metric Borel space with distance (2); reason: ρ is the only structure the paper uses on Θ; a subset of ℝˡ with ρ is an instance
--   - generalization: initial capacity c, sign unstated → every c ≥ 0, including cᵢ = 0; reason: at cᵢ < 0 (PCP) is infeasible; the source's c is a case
--   - encoding: RUB_T a maximum → real sSup; reason: attained or not, the inequality reads the same; x ≡ 0 is feasible
-- source:
--   Jiang, Li & Zhang, Online Stochastic Optimization with Wasserstein Based Non-stationarity, arXiv:2012.06961v3, Lemma 1, p.14; proof p.45

import Mathlib
import Definitions.Def_OnlineWass_Model
import Definitions.Def_OnlineWass_benchmarks

open MeasureTheory

namespace OnlineWass

/-- **Lemma 1, Jiang, Li & Zhang, arXiv:2012.06961v3, p.14 (proof p.45):** `R^UB_T ≥ 𝔼[R*_T]`, where
`θₜ ∼ 𝒫ₜ` are independent.

**Formalization Note.** `R*_T` is integrable by `OnlineWass.regret_wellDefined`. The correction
`f(0; θ) ≥ 0` is not a hypothesis here. -/
theorem lemma_1 {k m T : ℕ} {Θ : Type*} [MetricSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (M : Model k m Θ) (q : ℝ) (hA : Assumption1 M q) (hρ : DistEqRho M) (hT : 0 < T)
    (c : Fin m → ℝ) (hc : 0 ≤ c)
    (P : Fin T → Measure Θ) [∀ t, IsProbabilityMeasure (P t)] :
    ∫ H, offlineValue M c H ∂Measure.pi P ≤ fluidValue M c P := by sorry

end OnlineWass
