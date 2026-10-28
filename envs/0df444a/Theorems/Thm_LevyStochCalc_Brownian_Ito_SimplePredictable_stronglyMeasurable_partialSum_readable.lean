-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_stronglyMeasurable_partialSum_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.stronglyMeasurable_partialSum_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:48.705127+00:00
-- url     : https://prove2.me/theorems/fd1cc025-8f0a-4737-8e80-8b55eaf193de
-- title:
--   Strong Measurability of Partial Brownian Sums
-- statement:
--   This lemma proves strong measurability of a partial sum of the elementary Brownian integral.
--
--   Let $G$ be a simple predictable integrand, $W$ a Brownian motion under a probability measure $P$, and $\mathcal F$ a filtration for which $W$ is Brownian. Assume every coefficient $\xi_i$ of $G$ is strongly measurable with respect to the sigma-algebra at the corresponding tile's left endpoint. For $k\le N$, where $N$ is the number of tiles, the partial sum `SimplePredictable.partialSum` is strongly measurable with respect to the sigma-algebra at the partition time $\tau_k$:
--
--   $$
--   G.\operatorname{partialSum}(W,k):\Omega\to\mathbb R
--   \quad\text{is strongly measurable with respect to }\mathcal F_{\tau_k}.
--   $$
--
--   The result supplies the adaptedness needed for moment calculations and conditional-expectation arguments involving elementary stochastic integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito.SimplePredictable`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem stronglyMeasurable_partialSum (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
--       (hℱ : IsBrownianFiltration W ℱ)
--       (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (G.partition i.castSucc)) (G.ξ i))
--       {k : ℕ} (hk : k ≤ G.N) :
--       @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (G.partition ⟨k, by omega⟩)) (G.partialSum W k)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Previous: [`integral_mul_increment_pow`](https://prove2.me/theorems/8fc1f6bc-eb0f-42e8-a4c1-562b4c26ab81) · Next: [`varClock_mono`](https://prove2.me/theorems/ca4d3739-0c25-400e-91e5-2326905bc735).
--
--   [Source excerpt, lines 216–222](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean#L216-L222) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoFourthMomentIncrements`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.stronglyMeasurable_partialSum`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean, lines 216-239). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.stronglyMeasurable_partialSum_readable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {k : ℕ} (hk : k ≤ G.N) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition ⟨k, by omega⟩)) (G.partialSum W k) := by sorry
