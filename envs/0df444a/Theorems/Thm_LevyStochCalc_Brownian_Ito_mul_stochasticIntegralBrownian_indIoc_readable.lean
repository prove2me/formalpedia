-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_mul_stochasticIntegralBrownian_indIoc_readable
-- name    : LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:08.816832+00:00
-- url     : https://prove2.me/theorems/13bdf081-9a6f-4dc1-a40f-ce4f657ba4ff
-- title:
--   Pulling a Past Weight Into a Windowed Itô Integral
-- statement:
--   This formalizes the pull-out identity for a bounded weight known at the beginning of a time window.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, let $W$ be a Brownian motion under $P$, and let $\mathcal F$ be a filtration for which `hℱ` states that $W$ is Brownian. Let $0\le a<b$. Assume:
--
--   1. $V:\Omega\to\mathbb R$ is bounded, measurable, and strongly measurable with respect to $\mathcal F_a$.
--   2. $K:\Omega\times\mathbb R\to\mathbb R$ is jointly measurable and progressively measurable.
--   3. For every $T>0$, its $L^2$ energy is finite in the `ENNReal` sense:
--      $$
--      \int_\Omega\int_{[0,T]}\|K(\omega,s)\|_+^2\,ds\,dP<\top.
--      $$
--   4. The windowed integrand $\mathbf 1_{(a,b]}(s)K(\omega,s)$ is measurable, progressively measurable, and has finite energy on every positive horizon.
--   5. The weighted windowed integrand $V(\omega)\mathbf 1_{(a,b]}(s)K(\omega,s)$ is likewise measurable, progressively measurable, and has finite energy on every positive horizon.
--
--   Then for every $t>0$, the following equality holds $P$-almost everywhere:
--   $$
--   V(\omega)\,I_t\!\left[\mathbf 1_{(a,b]}K\right](\omega)
--   =
--   I_t\!\left[V\mathbf 1_{(a,b]}K\right](\omega),
--   $$
--   where $I_t$ denotes `stochasticIntegralBrownian`.
--
--   This is the main reusable pull-out identity for bounded information available before a window.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem mul_stochasticIntegralBrownian_indIoc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
--       {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
--       (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
--       (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
--       (hp : Probability.ProgressivelyMeasurable ℱ K)
--       (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (him : Measurable (Function.uncurry fun ω s => indIoc Ω a b ω s * K ω s))
--       (hip : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s * K ω s)
--       (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       (hvm : Measurable (Function.uncurry fun ω s => V ω * indIoc Ω a b ω s * K ω s))
--       (hvp : Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s * K ω s)
--       (hvq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
--         (‖V ω * indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {t : ℝ} (ht : 0 < t) :
--       (fun ω => V ω * stochasticIntegralBrownian W ℱ hℱ
--           (fun ω s => indIoc Ω a b ω s * K ω s) him hip hiq t ω)
--         =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
--           (fun ω s => V ω * indIoc Ω a b ω s * K ω s) hvm hvp hvq t
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoPullOut`](https://prove2.me/theorems/ec224d62-6516-4a47-919c-197424d19554).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/ItoIncrement`](https://prove2.me/theorems/0dacfd17-a335-4bce-a734-7c09a89723d3), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`stepIocMul_eval`](https://prove2.me/theorems/78e7de7a-b770-4a24-b582-8eedc3ca2e86), [`stepIocMul₀_eval`](https://prove2.me/theorems/56a8ce59-b36c-4fd6-8596-a506da0ad724), [`stochasticIntegralBrownian_indicator_Ioc`](https://prove2.me/theorems/bcc8c011-e83f-4b9e-a0e6-5de008451e39), [`stochasticIntegralBrownian_integralAgainst`](https://prove2.me/theorems/ad605701-48f4-400c-83de-f35b5212c9ce).
--
--   Previous: [`progressivelyMeasurable_mul_indIoc`](https://prove2.me/theorems/030165f7-acc3-4866-b777-afeba0e9b4de).
--
--   [Source excerpt, lines 176–195](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoPullOut.lean#L176-L195) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoPullOut.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoPullOut`, declaration `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoPullOut.lean, lines 172-241). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoPullOut

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoPullOut.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
include hℱ

theorem LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc_readable {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (him : Measurable (Function.uncurry fun ω s => indIoc Ω a b ω s * K ω s))
    (hip : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s * K ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hvm : Measurable (Function.uncurry fun ω s => V ω * indIoc Ω a b ω s * K ω s))
    (hvp : Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * indIoc Ω a b ω s * K ω s)
    (hvq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖V ω * indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    (fun ω => V ω * stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => indIoc Ω a b ω s * K ω s) him hip hiq t ω)
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => V ω * indIoc Ω a b ω s * K ω s) hvm hvp hvq t := by sorry
