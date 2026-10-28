-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_vectorTaylorRemainder_le_affine_readable
-- name    : LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:22.288591+00:00
-- url     : https://prove2.me/theorems/c50f87d4-01af-4809-9de8-adef3412ad18
-- title:
--   Integrated Vector Itô Taylor Remainder Bound
-- statement:
--   This theorem bounds the integrated absolute second-order Taylor remainder of a vector Itô process on a uniform grid. Let (Ω, P) be a probability space, let W be a d-dimensional Brownian motion with filtration ℱ, and let H, X₀, and bdrift satisfy the stated measurability, progressive measurability, and finite `ENNReal` energy hypotheses. Assume C ≥ 0 and |H(m,k,ω,s)| ≤ C. Assume X₀ is coordinatewise measurable. Let the drift be measurable, let B ≥ 0, and assume |bdrift(p,ω,s)| ≤ B. Let f : (Fin n → ℝ) → ℝ have everywhere-defined first and second Fréchet derivatives f′ and f″, with A ≥ 0, K ≥ 0, continuous f″, and ‖f″(z) − f″(w)‖ ≤ A + K‖z − w‖. For T > 0 and m ≠ 0, the function `taylorRemainderNormed` along the process `vectorItoProcess` sampled at `unifGrid T m` is integrable and its absolute integral is at most
--
--   $$A\,n\!\left[2B^2T\frac{T}{m}+2d^2C^2T\right]+K\,n^2\!\left[n\,4\!\left(m\left(B\frac{T}{m}\right)^3+d^2d\frac{C^2+(6+\texttt{gaussianFourthMoment})C^4}{2}\,T\sqrt{\frac{T}{m}}\right)\right].$$
--
--   The declaration `integral_abs_vectorTaylorRemainder_le_affine_readable` supplies an L¹ grid-error estimate for later Itô-formula arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_abs_vectorTaylorRemainder_le_affine (X₀ : Ω → Fin n → ℝ)
--       (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
--       (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
--       {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
--       {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
--       {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A)
--       (hK0 : 0 ≤ K) (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
--       (hf''c : Continuous f'') (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
--       {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
--       Integrable (fun ω : Ω => taylorRemainderNormed f f' f''
--           (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m) P
--         ∧ ∫ ω, |taylorRemainderNormed f f' f''
--             (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m| ∂P
--           ≤ A * ((n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))))
--             + K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
--               + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
--                 * (T * Real.sqrt (T / (m : ℝ)))))))))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoTaylor`](https://prove2.me/theorems/e2f63476-dcbb-4f48-b908-f9b176dad140).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Brownian/ItoFourthMomentIncrements`](https://prove2.me/theorems/e364d79c-aa3e-4099-9bf3-40950d2ed0f3), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/TaylorTwoVector`](https://prove2.me/theorems/7b95962e-e11d-4fe9-a26b-01c2fa7c2715), [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977).
--
--   Selected supporting theorems: [`integrable_norm_vectorItoProcess_sub_pow_three`](https://prove2.me/theorems/4ebc222e-11b8-4943-afb1-b14792258eba), [`integral_sq_norm_vectorItoProcess_sub_le`](https://prove2.me/theorems/4ad59ff0-71f2-424a-9d06-361263c34b7c), [`measurable_taylorRemainderNormed`](https://prove2.me/theorems/82f77efa-c25f-4464-bcbe-e2c70b974c2c), [`sum_integral_norm_vectorItoIncrement_pow_three_le`](https://prove2.me/theorems/9aa04438-e208-4383-a2ac-b7d722c248ed), [`sum_integral_sq_norm_vectorItoIncrement_le`](https://prove2.me/theorems/f8183882-c470-441e-b8d8-7efc9444036e).
--
--   Previous: [`sum_integral_sq_norm_vectorItoIncrement_le`](https://prove2.me/theorems/f8183882-c470-441e-b8d8-7efc9444036e).
--
--   [Source excerpt, lines 113–129](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoTaylor.lean#L113-L129) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoTaylor.lean#L110-L202 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoTaylor`, declaration `LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoTaylor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoTaylor.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
include hC0 hCH

theorem LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine_readable (X₀ : Ω → Fin n → ℝ)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A)
    (hK0 : 0 ≤ K) (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf''c : Continuous f'') (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => taylorRemainderNormed f f' f''
        (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m) P
      ∧ ∫ ω, |taylorRemainderNormed f f' f''
          (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m| ∂P
        ≤ A * ((n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))))
          + K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
            + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
              * (T * Real.sqrt (T / (m : ℝ))))))))) := by sorry
