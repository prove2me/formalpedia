-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_quadVarRiemann_decomp_ae_readable
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.quadVarRiemann_decomp_ae_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:57.163539+00:00
-- url     : https://prove2.me/theorems/99d689e6-7b6f-456b-80a4-7810d4f01658
-- title:
--   Almost-Everywhere Quadratic-Variation Riemann Decomposition
-- statement:
--   Let $X$ be a vector Itô process with bounded Brownian coefficients $|H^{m,k}|\le C$, measurable bounded drift $|b^m|\le B$, and the stated progressive-measurability and integrability assumptions. For coordinate indices $p,q$, a function $\phi$, $T>0$, and $m\ne0$, the weighted product sum over the uniform grid equals almost everywhere the sum of six groups: drift–drift terms, two drift–martingale terms, diagonal compensated products, off-diagonal Brownian cross terms, and the frozen Riemann sum
--
--   $$\sum_{i<m}\phi(X_{t_i})\int_{(t_i,t_{i+1}]}
--   \sum_k H^{p,k}_sH^{q,k}_s\,ds.$$
--
--   The equality is $P$-almost everywhere and uses `quadVarRiemann_decomp_ae_readable` exactly in that scope.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--                   - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m i) ω)))
--           + (∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
--               * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
--                   (hHp p k) (hHp q k) (hHs p k) (hHs q k)
--                   (unifGrid T m i) (unifGrid T m (i + 1)) ω)
--           + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
--               φ (X (unifGrid T m i) ω)
--                 * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
--                     (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
--           + ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
--               * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
--                   ∑ k : Fin d, H p k ω s * H q k ω s ∂volume
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition`](https://prove2.me/theorems/ea95ae2a-21bc-42c8-afc2-c6002d198e2b).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/CrossVariationSum`](https://prove2.me/theorems/a1ff2b05-5818-415f-a2f2-029a029a1d6c), [`LevyStochCalc/Brownian/ItoFormulaGrid`](https://prove2.me/theorems/7475fbad-28a8-4f84-8af7-d42e8a98672f), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977), [`LevyStochCalc/Brownian/PolarisedQuadVar`](https://prove2.me/theorems/00553e93-f879-4904-9333-b2c00471b79f), [`LevyStochCalc/Brownian/VectorItoProcessVersion`](https://prove2.me/theorems/16cf69d2-7364-41f8-b67f-c07cbbc711d4).
--
--   Supporting theorems: [`vectorItoMartingale_prod_eq`](https://prove2.me/theorems/13df531e-8950-45e0-98a1-a8e79fecabcc).
--
--   Previous: [`vectorItoMartingale_prod_eq`](https://prove2.me/theorems/13df531e-8950-45e0-98a1-a8e79fecabcc) · Next: [`IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le`](https://prove2.me/theorems/f3fde419-4acc-40a6-83f8-e6f5d5a9c736).
--
--   [Source excerpt, lines 181–192](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean#L181-L192) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean#L161-L256 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition`, declaration `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.quadVarRiemann_decomp_ae`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.quadVarRiemann_decomp_ae_readable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    (φ : (Fin n → ℝ) → ℝ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∀ᵐ ω ∂P, (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
      = (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume))
        + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
              * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
                - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)))
        + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume)
              * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m (i + 1)) ω
                - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m i) ω)))
        + (∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
            φ (X (unifGrid T m i) ω)
              * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                  (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by sorry
