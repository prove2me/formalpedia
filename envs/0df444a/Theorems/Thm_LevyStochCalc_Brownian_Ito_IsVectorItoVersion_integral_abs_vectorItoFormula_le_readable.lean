-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_vectorItoFormula_le_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_vectorItoFormula_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:40.849023+00:00
-- url     : https://prove2.me/theorems/a8042955-1689-46eb-aed6-78c0655a75f1
-- title:
--   L¹ Defect Bound for Vector Itô Formula
-- statement:
--   This theorem bounds the L¹ defect of the vector Itô formula on a uniform grid. Let (Ω, P) be a probability space, W a d-dimensional Brownian motion, ℱ a filtration, H a progressively measurable diffusion coefficient with the stated coordinatewise `ENNReal` square-energy conditions, and X a vector Itô version with initial value X₀ and drift bdrift. Assume H is bounded by C ≥ 0, the initial value and drift are measurable, and the drift is bounded by B ≥ 0. Let f : (Fin n → ℝ) → ℝ have everywhere-defined first and second Fréchet derivatives f′ and f″; assume ‖f′(z)‖ ≤ K₁, 0 ≤ K₂, ‖f″(z)‖ ≤ K₂, f″ is continuous, and ‖f″(z) − f″(w)‖ ≤ A + K‖z − w‖ with A, K ≥ 0. Assume the products involving `coordDeriv f′` and H are measurable, progressively measurable, and have finite `ENNReal` square energy. For T > 0 and m ≠ 0, the Itô defect is integrable and
--
--   $$\int\!\left|f(X_T)-f(X_0)-\left(D_T+M_T+\tfrac12 Q_T\right)\right|dP\le \operatorname{vectorItoGridError}(n,d,B,C,T,A,K,K_2,T/m),$$
--
--   where D_T, M_T, and Q_T are respectively the drift integral, stochastic-integral term, and quadratic-variation term displayed in the declaration. This is the quantitative finite-grid statement used to pass from the grid decomposition to vector Itô’s formula.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--             + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
--                 coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) P
--         ∧ ∫ ω, |f (X T ω) - f (X 0 ω)
--             - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
--                   coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
--               + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
--                   (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
--                   (hmg p k) (hpg p k) (hqg p k) T ω)
--               + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
--                   coordDeriv₂ f'' p q (X s ω)
--                     * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
--           ≤ vectorItoGridError (n : ℝ) (d : ℝ) B C T A K K₂ (T / (m : ℝ))
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoFormula`](https://prove2.me/theorems/fd5fe3af-3527-442e-9c98-db6ff7b03e09).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoL2CompletionMaster`](https://prove2.me/theorems/fa70df32-ed25-4a87-aa72-9a0ad14cc12f), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Selected supporting theorems: [`IsVectorItoVersion.integral_abs_frozenRiemann_sub_le`](https://prove2.me/theorems/d2663f69-ee63-4f38-b143-87d304d61dbb), [`IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le`](https://prove2.me/theorems/f3fde419-4acc-40a6-83f8-e6f5d5a9c736), [`IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le`](https://prove2.me/theorems/74d597a9-d0f7-4590-b8a5-d44291007272), [`IsVectorItoVersion.vectorItoFormula_decomp_ae`](https://prove2.me/theorems/33331f90-4a12-4797-b7d5-47e2dc7611ad), [`integral_abs_le_sqrt_of_lintegral_sq_le`](https://prove2.me/theorems/fabb0c45-93fb-4537-bc15-bc10719aac9e).
--
--   Next: [`IsVectorItoVersion.itoFormula`](https://prove2.me/theorems/9fc109b4-701c-4220-bf8e-2dcb0c672023).
--
--   [Source excerpt, lines 137–148](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoFormula.lean#L137-L148) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoFormula.lean#L104-L354 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoFormula`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_vectorItoFormula_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormula

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormula.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
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
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)
include hC0 hCH

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_vectorItoFormula_le_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K) (hf''c : Continuous f'')
    (hf''aff : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) P
      ∧ ∫ ω, |f (X T ω) - f (X 0 ω)
          - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
        ≤ vectorItoGridError (n : ℝ) (d : ℝ) B C T A K K₂ (T / (m : ℝ)) := by sorry
