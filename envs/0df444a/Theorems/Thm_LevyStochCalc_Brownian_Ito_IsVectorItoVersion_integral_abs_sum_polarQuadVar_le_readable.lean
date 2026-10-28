-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_sum_polarQuadVar_le_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_polarQuadVar_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:25.233674+00:00
-- url     : https://prove2.me/theorems/015954d3-b039-4b49-87c9-35a017fa7c3b
-- title:
--   L¹ Bound for Diagonal Polarized Grid Sums
-- statement:
--   Consider a $d$-dimensional Brownian motion, a vector Itô process $X$ with $n$ coordinates, and coordinate integrands bounded in absolute value by $C\ge0$. Let $p,q\in\mathrm{Fin}(n)$ and $k\in\mathrm{Fin}(d)$, and assume the required measurability, progressive-measurability, integrability, and sum-integrand hypotheses. If $\phi$ is continuous, $|\phi(x)|\le K_\phi$ with $K_\phi\ge0$, $T>0$, and $m\ne0$, then the weighted diagonal sum is integrable and
--
--   $$\mathbb E\left|\sum_{i<m}\phi(X_{t_i})\,\mathrm{polarQuadVarIncrement}_{t_i,t_{i+1}}(H^{p,k},H^{q,k})\right|
--   \le\sqrt{K_\phi^2\,3\bigl(2(6+\gamma_4)+2\bigr)(2C)^4\frac{T^2}{m}},$$
--
--   where $t_i=\mathrm{unifGrid}(T,m,i)$. The conclusion is an $L^1$ bound of order $m^{-1/2}$.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsVectorItoVersion.integral_abs_sum_polarQuadVar_le
--       (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (p q : Fin n) (k : Fin d)
--       (hma : Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
--       (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
--       (hqa : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
--         (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
--       {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
--       (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
--       Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
--           * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
--               (hHp p k) (hHp q k) (hHs p k) (hHs q k)
--               (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
--         ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
--             * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
--                 (hHp p k) (hHp q k) (hHs p k) (hHs q k)
--                 (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
--           ≤ Real.sqrt (Kφ ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
--             * (T ^ 2 / (m : ℝ)))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds`](https://prove2.me/theorems/e506e7f3-bd3b-40cf-9c41-baaea27e3be9).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/PolarisedQuadVar`](https://prove2.me/theorems/00553e93-f879-4904-9333-b2c00471b79f), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`integral_sq_weighted_polarQuadVarSum_le`](https://prove2.me/theorems/194ed6f8-bb43-4c00-b88b-c7080958b1e9), [`memLp_two_polarQuadVarIncrement`](https://prove2.me/theorems/e1f3d644-9e95-4545-bc1a-84c062eb6f44), [`stronglyMeasurable_polarQuadVarIncrement`](https://prove2.me/theorems/257fc5bd-0d48-42b0-a71b-4fcd26b462bd), [`integral_abs_le_sqrt_of_integral_sq_le`](https://prove2.me/theorems/bfdc1797-b9af-45f2-9493-fd8068fd1149).
--
--   Previous: [`IsVectorItoVersion.integral_abs_sum_driftCross_le`](https://prove2.me/theorems/99d8a7b4-fa07-42fc-9e39-4441e680b3f8) · Next: [`IsVectorItoVersion.integral_abs_sum_offDiagCross_le`](https://prove2.me/theorems/fedb1c53-feeb-4afa-893e-6fa8c0db0d02).
--
--   [Source excerpt, lines 282–299](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean#L282-L299) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean#L280-L335 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_polarQuadVar_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_polarQuadVar_le_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (p q : Fin n) (k : Fin d)
    (hma : Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * (T ^ 2 / (m : ℝ))) := by sorry
