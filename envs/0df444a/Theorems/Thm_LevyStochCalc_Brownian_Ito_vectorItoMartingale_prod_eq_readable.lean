-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_vectorItoMartingale_prod_eq_readable
-- name    : LevyStochCalc.Brownian.Ito.vectorItoMartingale_prod_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:51.918338+00:00
-- url     : https://prove2.me/theorems/13df531e-8950-45e0-98a1-a8e79fecabcc
-- title:
--   Vector Martingale Increment Product Decomposition
-- statement:
--   For a multidimensional Brownian-driven vector Itô process, let $p,q$ be coordinate indices, let $0\le u\le v$, and fix $\omega$. Assume the coefficient bounds $C\ge0$ and $|H^{m,k}|\le C$. The product of the martingale-part increments decomposes as
--
--   $$\Delta M^p\,\Delta M^q
--   =\sum_k\mathrm{polarQuadVarIncrement}^{k}_{u,v}
--   +\sum_k\int_{(u,v]}H^{p,k}H^{q,k}\,ds
--   +\sum_k\sum_{\ell\ne k}\mathrm{crossIncrement}^{k,\ell}_{u,v}.$$
--
--   The sums range over $k,\ell\in\mathrm{Fin}(d)$, with the off-diagonal sum represented by `Finset.univ.erase k`. This is a pointwise algebraic decomposition.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem vectorItoMartingale_prod_eq (p q : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (ω : Ω) :
--       (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
--           - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
--         * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
--           - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
--         = (∑ k : Fin d, polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
--               (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
--           + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
--           + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
--               crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
--                 (hHs q l) k l u v ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition`](https://prove2.me/theorems/ea95ae2a-21bc-42c8-afc2-c6002d198e2b).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/CrossVariationSum`](https://prove2.me/theorems/a1ff2b05-5818-415f-a2f2-029a029a1d6c), [`LevyStochCalc/Probability/Progressive`](https://prove2.me/theorems/791c3db2-fda1-4ce1-b670-1f4c83fc16b4), [`LevyStochCalc/Brownian/VectorItoProcess`](https://prove2.me/theorems/d4d82e30-d82f-4554-8daf-ab3d61a8d977), [`LevyStochCalc/Brownian/PolarisedQuadVar`](https://prove2.me/theorems/00553e93-f879-4904-9333-b2c00471b79f).
--
--   Next: [`IsVectorItoVersion.quadVarRiemann_decomp_ae`](https://prove2.me/theorems/99d689e6-7b6f-456b-80a4-7810d4f01658).
--
--   [Source excerpt, lines 81–91](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean#L81-L91) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/VectorItoQuadVarRiemannDecomposition.lean#L78-L159 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition`, declaration `LevyStochCalc.Brownian.Ito.vectorItoMartingale_prod_eq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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

theorem LevyStochCalc.Brownian.Ito.vectorItoMartingale_prod_eq_readable (p q : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (ω : Ω) :
    (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
      * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
      = (∑ k : Fin d, polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
        + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
        + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
            crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l u v ω := by sorry
