-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_frozenRiemann_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_frozenRiemann_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:47.786796+00:00
-- url     : https://prove2.me/theorems/d2663f69-ee63-4f38-b143-87d304d61dbb
-- title:
--   L¹ Error Bound for a Frozen-Weight Riemann Sum
-- statement:
--   This is an $L^1$ error estimate for a frozen-weight Riemann sum along a vector Itô process.
--
--   Let $X$ be a vector Itô-process version with $n$ state coordinates and $d$ Brownian drivers. Assume the diffusion entries are measurable, progressively measurable, square-integrable on positive intervals, and bounded by $C\ge0$; assume the drift is measurable and bounded by $B\ge0$. Let $wgt(\omega,s)$ be measurable with $|wgt(\omega,s)|\le A$ for $A\ge0$. Let $\phi:\mathrm{Fin}(n)\to\mathbb R\to\mathbb R$ be continuous, satisfy $|\phi(x)|\le K_\phi$, and obey
--   $$
--   |\phi(x)-\phi(y)|\le M_\phi+L\|x-y\|,
--   $$
--   with $M_\phi,L\ge0$. If $T>0$ and $m\ne0$, then the frozen sum is integrable and
--   $$
--   \int\left|\sum_{i<m}\phi(X_{t_i})\int_{(t_i,t_{i+1}]}wgt_s\,ds
--   -\int_{(0,T]}\phi(X_s)wgt_s\,ds\right|dP
--   \le M_\phi AT+LA T\,n\left(B\frac{T}{m}+dC\sqrt{\frac{T}{m}}\right),
--   $$
--   where $t_i=\texttt{unifGrid}(T,m,i)$.
--
--   The statement quantifies the approximation error used in time-integral convergence arguments for vector Itô processes.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsVectorItoVersion.integral_abs_frozenRiemann_sub_le
--       (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
--       (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
--       (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
--       (wgt : Ω → ℝ → ℝ) (hwm : Measurable (Function.uncurry wgt))
--       {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ (ω : Ω) (s : ℝ), |wgt ω s| ≤ A)
--       {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
--       {Mφ L : ℝ} (hMφ0 : 0 ≤ Mφ) (hL0 : 0 ≤ L)
--       (hφaff : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ Mφ + L * ‖x - y‖)
--       {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
--       Integrable (fun ω : Ω =>
--           (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
--               * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), wgt ω s ∂volume)
--             - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume) P
--         ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
--               * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), wgt ω s ∂volume)
--             - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| ∂P
--           ≤ Mφ * A * T + L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
--             + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoTimeRiemann`](https://prove2.me/theorems/ca4d7cff-196a-4a66-a466-8bfacc2957bb).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`IsVectorItoVersion.lintegral_window_norm_sub_le`](https://prove2.me/theorems/f3184ccd-0e0a-4340-b558-ebc13c8392fd), [`abs_setIntegral_Ioc_le`](https://prove2.me/theorems/7eab41d0-09a0-484b-9388-f6640a71836d).
--
--   [Source excerpt, lines 51–69](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoTimeRiemann.lean#L51-L69) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoTimeRiemann.lean#L47-L334 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoTimeRiemann`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_frozenRiemann_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoTimeRiemann

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoTimeRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_frozenRiemann_sub_le_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    (wgt : Ω → ℝ → ℝ) (hwm : Measurable (Function.uncurry wgt))
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ (ω : Ω) (s : ℝ), |wgt ω s| ≤ A)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {Mφ L : ℝ} (hMφ0 : 0 ≤ Mφ) (hL0 : 0 ≤ L)
    (hφaff : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ Mφ + L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω =>
        (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| ∂P
        ≤ Mφ * A * T + L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by sorry
