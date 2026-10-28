-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_seq_ae_tendsto_stochInt_clamp_readable
-- name    : LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_clamp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:36.72011+00:00
-- url     : https://prove2.me/theorems/bdc5e606-3379-4cae-bf91-d24473c129d6
-- title:
--   Almost-Sure Subsequence Convergence of Clamped Stochastic Integrals
-- statement:
--   Under the Brownian, filtration, bounded-derivative, measurability, progressive-measurability, and finite-energy hypotheses for the clamped and limiting diffusion integrands, assume $Y_i\to X$ almost everywhere on a positive window $[0,T]$. Then there exists $m:\mathbb N\to\mathbb N$ with $i\le m(i)$ such that for almost every $\omega$, every $p\in\mathrm{Fin}\,n$ and $k\in\mathrm{Fin}\,d$,
--
--   $$
--   \int_0^T \partial_p f'(Y_{m(i)})\,\operatorname{clampCoeff}(H,n_{m(i)})_{pk}\,dW^k
--   \longrightarrow
--   \int_0^T \partial_p f'(X)H_{pk}\,dW^k.
--   $$
--
--   The displayed notation abbreviates the corresponding `stochasticIntegralBrownian` terms with their explicit hypotheses.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--       (hpX : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
--         fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
--       (hqX : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
--         ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--           (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
--       ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧ ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
--         Filter.Tendsto (fun i : ℕ => stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
--             (fun ω s => coordDeriv f' p (Y (ms i) s ω) * clampCoeff H (ns (ms i)) p k ω s)
--             (hmY (ms i) p k) (hpY (ms i) p k) (hqY (ms i) p k) T ω) Filter.atTop
--           (𝓝 (stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
--             (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
--             (hmX p k) (hpX p k) (hqX p k) T ω))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/ItoFormulaUnboundedLimit`](https://prove2.me/theorems/8c696e51-9810-4fbb-b0f0-ded116e9b79e).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d), [`LevyStochCalc/Ito/ItoFormulaUnboundedClamp`](https://prove2.me/theorems/086dfa78-0e92-44fe-ad09-837cbf3527cb), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4).
--
--   Supporting theorems: [`exists_seq_ae_tendsto_of_tendsto_lintegral`](https://prove2.me/theorems/3562f88f-3c78-4ff5-ad93-01edc45ad90f), [`tendsto_energy_diffusionIntegrand_clamp`](https://prove2.me/theorems/9cee699e-7563-482a-af58-2791b1f7cffd).
--
--   Next: [`itoFormula_of_unbounded_coeff`](https://prove2.me/theorems/26b3bb9f-845f-407e-8e95-6d9fce1413b9).
--
--   [Source excerpt, lines 112–123](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean#L112-L123) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean#L87-L142 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.ItoFormulaUnboundedLimit`, declaration `LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_clamp`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ')

theorem LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_clamp_readable
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ} (hT : 0 < T)
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (hmY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s))
    (hpY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
    (hqY : ∀ (i : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmX : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpX : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqX : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧ ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      Filter.Tendsto (fun i : ℕ => stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => coordDeriv f' p (Y (ms i) s ω) * clampCoeff H (ns (ms i)) p k ω s)
          (hmY (ms i) p k) (hpY (ms i) p k) (hqY (ms i) p k) T ω) Filter.atTop
        (𝓝 (stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
          (hmX p k) (hpX p k) (hqX p k) T ω)) := by sorry
