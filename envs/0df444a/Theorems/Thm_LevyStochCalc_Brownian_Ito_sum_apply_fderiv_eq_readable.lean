-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_apply_fderiv_eq_readable
-- name    : LevyStochCalc.Brownian.Ito.sum_apply_fderiv_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:13.542571+00:00
-- url     : https://prove2.me/theorems/77c8b45b-4dd4-41fe-8c61-8f62aefbbe0d
-- title:
--   Coordinate Decomposition of the First-Order Taylor Sum
-- statement:
--   This is the first-order Taylor-sum decomposition for a vector Itô-process version.
--
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $W$ be a $d$-dimensional Brownian motion with coordinate Brownian filtrations, and let $H_{pk}$ satisfy measurability, progressive measurability, and finite squared extended-integral assumptions. Let $X$ be an `IsVectorItoVersion` with measurable drifts $b_p$. Assume that the drifts are bounded in absolute value by $B\in\mathbb R$ (without a separate nonnegativity assumption), let $f'$ be a continuous linear map-valued function on $\operatorname{Fin}(n)\to\mathbb R$, and let $T>0$ and $m\ne0$.
--
--   For almost every $\omega$,
--   $$
--   \begin{aligned}
--   \sum_{i<m} f'(X_{t_i})\bigl(X_{t_{i+1}}-X_{t_i}\bigr)
--   ={}&\sum_p\sum_{i<m}\partial_p f'(X_{t_i})\int_{(t_i,t_{i+1}]} b_p(\omega,s)\,ds\\
--   &+\sum_p\sum_k\sum_{i<m}\partial_p f'(X_{t_i})
--   \bigl(I_{pk}(t_{i+1},\omega)-I_{pk}(t_i,\omega)\bigr),
--   \end{aligned}
--   $$
--   where $t_i=\operatorname{unifGrid}(T,m,i)$ and $I_{pk}$ is `coordItoIntegral`.
--
--   This identity isolates the drift and martingale Riemann sums in the vector Itô decomposition.
--
--   **Formalization Note** The equality is almost everywhere with respect to $P$; `coordDeriv`, `coordItoIntegral`, and `unifGrid` are the relevant Lean definitions.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_apply_fderiv_eq
--       (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
--       (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ}
--       (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
--       (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
--       ∀ᵐ ω ∂P, ∑ i ∈ Finset.range m, f' (X (unifGrid T m i) ω)
--             (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω)
--         = (∑ p : Fin n, ∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
--               * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
--           + ∑ p : Fin n, ∑ k : Fin d, ∑ i ∈ Finset.range m,
--               coordDeriv f' p (X (unifGrid T m i) ω)
--                 * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
--                   - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoFormulaDecomp`](https://prove2.me/theorems/8f8fed5f-bb75-4985-83e7-6765eeac8110).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/CoordDerivative`](https://prove2.me/theorems/48f1793d-d529-4536-81b1-f98ae2c3d13d), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`sum_range_add_sum_comm`](https://prove2.me/theorems/3691605f-5bd6-4983-af72-18ade5e5f6bc).
--
--   Previous: [`sum_apply_fderiv₂_eq`](https://prove2.me/theorems/e68e16a1-d8ff-49b3-9798-30a9e8ff8724) · Next: [`IsVectorItoVersion.vectorItoFormula_decomp_ae`](https://prove2.me/theorems/33331f90-4a12-4797-b7d5-47e2dc7611ad).
--
--   [Source excerpt, lines 122–134](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean#L122-L134) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean#L118-L163 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoFormulaDecomp`, declaration `LevyStochCalc.Brownian.Ito.sum_apply_fderiv_eq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.sum_apply_fderiv_eq_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ}
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∀ᵐ ω ∂P, ∑ i ∈ Finset.range m, f' (X (unifGrid T m i) ω)
          (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω)
      = (∑ p : Fin n, ∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        + ∑ p : Fin n, ∑ k : Fin d, ∑ i ∈ Finset.range m,
            coordDeriv f' p (X (unifGrid T m i) ω)
              * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
                - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω) := by sorry
