-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_quadVarRiemann_sub_le_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:26.675376+00:00
-- url     : https://prove2.me/theorems/f3fde419-4acc-40a6-83f8-e6f5d5a9c736
-- title:
--   L¹ Rate for Weighted Quadratic-Variation Riemann Sums
-- statement:
--   Let $X$ be a vector Itô process with $n$ coordinates and $d$ Brownian drivers. Assume $C\ge0$, $|H^{m,k}|\le C$, $B\ge0$, $|b^m|\le B$, the stated measurability and square-integrability conditions, and the required conditions for $H^{p,k}+H^{q,k}$. Let $\phi$ be continuous, bounded by $K_\phi$, and satisfy
--   $|\phi(x)-\phi(y)|\le M_\phi+L\|x-y\|$ with $M_\phi,L\ge0$. For $T>0$ and $m\ne0$, the weighted coordinate-increment Riemann sum minus its target integral is integrable and its first absolute moment is at most
--
--   $$mK_\phi\left(B\frac{T}{m}\right)^2
--   +2mK_\phi\left(B\frac{T}{m}\right)dC\sqrt{\frac{T}{m}}
--   +d\sqrt{K_\phi^2\,3(2(6+\gamma_4)+2)(2C)^4\frac{T^2}{m}}$$
--
--   $$+d^2\sqrt{K_\phi^2(6+\gamma_4)\frac{C^4+C^4}{2}\frac{T^2}{m}}
--   +M_\phi dC^2T+LdC^2T\,n\left(B\frac{T}{m}+dC\sqrt{\frac{T}{m}}\right).$$
--
--   Here the grid is $t_i=\mathrm{unifGrid}(T,m,i)$ and the target is $\int_{(0,T]}\phi(X_s)\sum_kH^{p,k}_sH^{q,k}_s\,ds$.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--               φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume| ∂P
--         ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2)
--           + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
--           + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
--           + (d : ℝ) * Real.sqrt (Kφ ^ 2
--               * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ)))
--           + (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
--               * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
--           + (Mφ * ((d : ℝ) * C ^ 2) * T
--             + L * ((d : ℝ) * C ^ 2)
--               * (T * ((n : ℝ) * (B * (T / (m : ℝ))
--                 + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition`](https://prove2.me/theorems/ea95ae2a-21bc-42c8-afc2-c6002d198e2b).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Selected supporting theorems: [`IsVectorItoVersion.integral_abs_frozenRiemann_sub_le`](https://prove2.me/theorems/d2663f69-ee63-4f38-b143-87d304d61dbb), [`IsVectorItoVersion.integral_abs_sum_driftCross_le`](https://prove2.me/theorems/99d8a7b4-fa07-42fc-9e39-4441e680b3f8), [`IsVectorItoVersion.integral_abs_sum_drift_sq_le`](https://prove2.me/theorems/23639e5d-857a-4a6f-b70d-931626366848), [`IsVectorItoVersion.integral_abs_sum_offDiagCross_le`](https://prove2.me/theorems/fedb1c53-feeb-4afa-893e-6fa8c0db0d02), [`IsVectorItoVersion.integral_abs_sum_polarQuadVar_le`](https://prove2.me/theorems/015954d3-b039-4b49-87c9-35a017fa7c3b).
--
--   Previous: [`IsVectorItoVersion.quadVarRiemann_decomp_ae`](https://prove2.me/theorems/99d689e6-7b6f-456b-80a4-7810d4f01658).
--
--   [Source excerpt, lines 284–295](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean#L284-L295) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean#L258-L437 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannDecomposition

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    (hma : ∀ k : Fin d, Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ k : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {Mφ L : ℝ} (hMφ0 : 0 ≤ Mφ) (hL0 : 0 ≤ L)
    (hφaff : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ Mφ + L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume| ∂P
      ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (d : ℝ) * Real.sqrt (Kφ ^ 2
            * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ)))
        + (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
            * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
        + (Mφ * ((d : ℝ) * C ^ 2) * T
          + L * ((d : ℝ) * C ^ 2)
            * (T * ((n : ℝ) * (B * (T / (m : ℝ))
              + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by sorry
