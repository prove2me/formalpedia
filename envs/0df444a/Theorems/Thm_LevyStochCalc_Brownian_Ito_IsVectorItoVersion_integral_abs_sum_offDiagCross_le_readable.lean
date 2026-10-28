-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_sum_offDiagCross_le_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_offDiagCross_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:20.037755+00:00
-- url     : https://prove2.me/theorems/fedb1c53-feeb-4afa-893e-6fa8c0db0d02
-- title:
--   Absolute Bound for Off-Diagonal Cross Terms
-- statement:
--   This theorem bounds the expected absolute value of off-diagonal Brownian cross terms in a vector Itô process.
--
--   Let $W$ be a $d$-dimensional Brownian motion, let $X$ be a vector Itô process with coefficients $H$, and assume the stated `IsVectorItoVersion` hypotheses. Suppose $C\ge0$ and every coefficient $H_{mk}$ is bounded in absolute value by $C$. Let $p,q\in\operatorname{Fin}(n)$, let distinct Brownian coordinates $k\ne l$, let $\phi:\mathbb R^n\to\mathbb R$ be continuous and bounded by $K_\phi\ge0$, and let $T>0$ and $m\ne0$. Then the relevant cross-term sum is integrable and
--
--   $$
--   \mathbb E\left|\sum_{i<m}\phi(X_{t_i})\,\Delta_i^{k,l}\right|
--   \le
--   \sqrt{K_\phi^2\frac{(6+\mathsf g_4)(C^4+C^4)}{2}\frac{T^2}{m}}.
--   $$
--
--   Here $t_i=\operatorname{unifGrid}(T,m,i)$ and $\Delta_i^{k,l}$ is the product of the two coordinate Itô-integral increments on the grid cell. The estimate records the $m^{-1/2}$ decay of off-diagonal cross terms.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsVectorItoVersion.integral_abs_sum_offDiagCross_le
--       (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
--       (p q : Fin n)
--       {k l : Fin d} (hkl : k ≠ l)
--       {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
--       (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
--       Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
--           * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
--               k l (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
--         ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
--             * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
--                 k l (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
--           ≤ Real.sqrt (Kφ ^ 2 * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
--             * (T ^ 2 / (m : ℝ)))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds`](https://prove2.me/theorems/e506e7f3-bd3b-40cf-9c41-baaea27e3be9).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/CrossVariationSum`](https://prove2.me/theorems/a1ff2b05-5818-415f-a2f2-029a029a1d6c), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`integrable_sq_mul_and_le`](https://prove2.me/theorems/9194c79a-683c-4a17-8bf7-6d933792ea69), [`integral_sq_weighted_crossSum_le`](https://prove2.me/theorems/5d328781-1a8c-43bf-be55-0a5141e07939), [`integral_sub_pow_four_le`](https://prove2.me/theorems/12ff2533-d8a3-4978-a4f3-a45469d7fa7c), [`integral_abs_le_sqrt_of_integral_sq_le`](https://prove2.me/theorems/bfdc1797-b9af-45f2-9493-fd8068fd1149).
--
--   Previous: [`IsVectorItoVersion.integral_abs_sum_polarQuadVar_le`](https://prove2.me/theorems/015954d3-b039-4b49-87c9-35a017fa7c3b).
--
--   [Source excerpt, lines 339–352](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean#L339-L352) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean#L337-L382 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_offDiagCross_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
include hC0 hCH

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_offDiagCross_le_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (p q : Fin n)
    {k l : Fin d} (hkl : k ≠ l)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
            k l (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
              k l (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
          * (T ^ 2 / (m : ℝ))) := by sorry
