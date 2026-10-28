-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_condExp_mul_cross_increment_eq_zero_readable
-- name    : LevyStochCalc.Brownian.Ito.condExp_mul_cross_increment_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:08.028215+00:00
-- url     : https://prove2.me/theorems/99d0dc79-016a-4aa6-9626-db8a484a0275
-- title:
--   Conditional Centering of Cross Increments
-- statement:
--   This is a technical conditional-centering statement for cross increments of Itô integrals driven by distinct Brownian coordinates.
--
--   Let $(\Omega,\mathcal A,P)$ be a probability space, let $\mathcal F$ be a filtration, and let $W$ be a $d$-dimensional Brownian motion whose coordinates are Brownian motions relative to $\mathcal F$. Let $H,K:\Omega\times\mathbb R\to\mathbb R$ be jointly measurable and progressively measurable, and assume that for every $T>0$ their squared norms have finite $[0,\infty]$-valued integral over $\Omega\times[0,T]$. For distinct coordinates $i,j\in\operatorname{Fin}(d)$ and times $0\le a<b$, the conditional expectation at time $a$ of the product of the two Itô-integral increments is almost everywhere zero:
--
--   $$
--   \mathbb E\!\left[\left(\int_a^b H_s\,dW^i_s\right)
--   \left(\int_a^b K_s\,dW^j_s\right)\middle|\mathcal F_a\right]=0
--   \quad P\text{-a.e.}
--   $$
--
--   Here the conditional expectation is the Lean definition `condExp`, and the stochastic integrals are `stochasticIntegralBrownian`; the hypotheses include the stated measurability, progressive measurability, and finite squared-norm integrability conditions for both integrands. The result is reusable whenever cross-coordinate Itô increments must be treated as martingale differences.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem condExp_mul_cross_increment_eq_zero {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a)
--       (hab : a < b) :
--       P[fun ω => (stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
--             - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
--           * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
--             - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω) | ℱ a]
--         =ᵐ[P] 0
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossVariation`](https://prove2.me/theorems/1ab4e629-ed7f-48bb-b1cc-41ccac0e463c).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`integral_mul_cross_increment_eq_zero`](https://prove2.me/theorems/a33f4ff0-a082-4e43-a699-dd56f6c0e63a).
--
--   Previous: [`integral_mul_cross_increment_eq_zero`](https://prove2.me/theorems/a33f4ff0-a082-4e43-a699-dd56f6c0e63a).
--
--   [Source excerpt, lines 269–275](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossVariation.lean#L269-L275) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossVariation.lean (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossVariation`, declaration `LevyStochCalc.Brownian.Ito.condExp_mul_cross_increment_eq_zero`; the repository is private at upload time); vendored copy patched by formalization/vendor/port.patch (project file formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossVariation.lean, lines 266-307). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariation

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossVariation.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
variable {d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)

theorem LevyStochCalc.Brownian.Ito.condExp_mul_cross_increment_eq_zero_readable {i j : Fin d} (hij : i ≠ j) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) :
    P[fun ω => (stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - stochasticIntegralBrownian (W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * (stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs b ω
          - stochasticIntegralBrownian (W.W j) ℱ (hcoord j) K hKm hKp hKs a ω) | ℱ a]
      =ᵐ[P] 0 := by sorry
