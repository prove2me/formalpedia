-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_vectorItoFormula_decomp_ae_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.vectorItoFormula_decomp_ae_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:04.514728+00:00
-- url     : https://prove2.me/theorems/33331f90-4a12-4797-b7d5-47e2dc7611ad
-- title:
--   Almost-Everywhere Grid Decomposition of Vector Itô Formula
-- statement:
--   This is the grid decomposition of the vector Itô formula.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $W$ be a $d$-dimensional Brownian motion with coordinate Brownian filtrations, and let $H_{pk}$ satisfy the stated measurability, progressive measurability, and finite squared extended-integral assumptions. Let $X$ be an `IsVectorItoVersion` with measurable drifts $b_p$ bounded by $B$, and let $f,f',f''$ be a function and first and second derivative data. Assume that each process $\partial_p f'(X_s)H_{pk}(s)$ is measurable, progressively measurable, and has finite squared extended integral on every positive interval. Let $T>0$ and $m\ne0$.
--
--   The defect of the continuous-time expression equals, $P$-almost everywhere, the Taylor remainder plus the drift, martingale, and quadratic-variation grid errors:
--   $$
--   \begin{aligned}
--   &f(X_T)-f(X_0)-\Bigg[\sum_p\int_{(0,T]}\partial_p f'(X_s)b_p(s)\,ds
--   +\sum_{p,k}\int_0^T\partial_p f'(X_s)H_{pk}(s)\,dW_s^k\\
--   &\qquad\qquad+\frac12\sum_{p,q}\int_{(0,T]}\partial_{pq}f''(X_s)\sum_kH_{pk}(s)H_{qk}(s)\,ds\Bigg]
--   \\
--   ={}&\text{Taylor remainder on the grid}\\
--   &+\text{drift grid sum minus drift integral}\\
--   &+\text{martingale grid sum minus stochastic integral}\\
--   &+\text{quadratic-variation grid sum minus its time integral}.
--   \end{aligned}
--   $$
--   The four terms on the right are exactly those defined in the Lean statement through `taylorRemainderNormed`, `coordDeriv`, `coordDeriv₂`, `coordItoIntegral`, and `stochasticIntegralBrownian`.
--
--   This declaration packages the algebraic decomposition that precedes estimates and convergence arguments for the vector Itô formula.
--
--   **Formalization Note** The equality is an a.e. equality under $P$; the grid is `unifGrid`, and all time integrals use the interval $(0,T]$.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--                   * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
--                     - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))
--                 - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
--                     (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
--                     (hmg p k) (hpg p k) (hqg p k) T ω))
--           + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
--               ((∑ i ∈ Finset.range m, coordDeriv₂ f'' p q (X (unifGrid T m i) ω)
--                   * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
--                     * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
--                 - ∫ s in Set.Ioc (0 : ℝ) T,
--                     coordDeriv₂ f'' p q (X s ω)
--                       * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoFormulaDecomp`](https://prove2.me/theorems/8f8fed5f-bb75-4985-83e7-6765eeac8110).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/TaylorTwoVector`](https://prove2.me/theorems/7b95962e-e11d-4fe9-a26b-01c2fa7c2715), [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`sum_apply_fderiv_eq`](https://prove2.me/theorems/77c8b45b-4dd4-41fe-8c61-8f62aefbbe0d), [`sum_apply_fderiv₂_eq`](https://prove2.me/theorems/e68e16a1-d8ff-49b3-9798-30a9e8ff8724).
--
--   Previous: [`sum_apply_fderiv_eq`](https://prove2.me/theorems/77c8b45b-4dd4-41fe-8c61-8f62aefbbe0d).
--
--   [Source excerpt, lines 196–207](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean#L196-L207) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean#L165-L220 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoFormulaDecomp`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.vectorItoFormula_decomp_ae`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormulaDecomp

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.vectorItoFormula_decomp_ae_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ}
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume))
      =ᵐ[P] fun ω : Ω =>
        taylorRemainderNormed f f' f'' (fun i => X (unifGrid T m i) ω) m
        + (∑ p : Fin n, ((∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * bdrift p ω s ∂volume))
        + (∑ p : Fin n, ∑ k : Fin d,
            ((∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
                * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
                  - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))
              - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                  (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
                  (hmg p k) (hpg p k) (hqg p k) T ω))
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            ((∑ i ∈ Finset.range m, coordDeriv₂ f'' p q (X (unifGrid T m i) ω)
                * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
                  * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
              - ∫ s in Set.Ioc (0 : ℝ) T,
                  coordDeriv₂ f'' p q (X s ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) := by sorry
