-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_crossSum_sq_readable
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_crossSum_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:41.454255+00:00
-- url     : https://prove2.me/theorems/ef40178c-963c-4c39-b6b5-7722afb01efd
-- title:
--   Second Moment of a Discrete Cross-Increment Sum
-- statement:
--   This is the exact second-moment identity for cross products of distinct Brownian coordinates on a uniform grid.
--
--   Let $W$ be a $d$-dimensional Brownian motion, let $i,j\in\mathrm{Fin}(d)$ be distinct, and let $\mathcal F$ make every coordinate a Brownian motion. For $a\ge0$, $h>0$, and $m\in\mathbb N$, define the grid points $s_k=\texttt{affineGrid}(a,h,k)$. Then the cross-increment sum is square-integrable and
--   $$
--   \int\left(\sum_{k<m}(W^i_{s_{k+1}}-W^i_{s_k})(W^j_{s_{k+1}}-W^j_{s_k})\right)^2dP
--   =mh^2.
--   $$
--
--   This identity is the discrete variance calculation underlying the direct cross-orthogonality argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma integral_crossSum_sq (W : MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
--       {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
--       {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) :
--       Integrable (fun ω => (∑ k ∈ Finset.range m,
--           ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
--             * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2) P
--       ∧ ∫ ω, (∑ k ∈ Finset.range m,
--           ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
--             * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2 ∂P
--         = m * h ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossOrthogonalityDirectCross`](https://prove2.me/theorems/fd42d764-e99f-4994-8020-f8822509f5ef).
--
--   Definition modules: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`integral_mul_increment_pow`](https://prove2.me/theorems/8fc1f6bc-eb0f-42e8-a4c1-562b4c26ab81), [`integral_pow_gaussianReal_zero`](https://prove2.me/theorems/5bcebbba-553a-4972-8595-83ab7dcceb2b).
--
--   Next: [`integral_mul_increment_mul_increment_eq_crossSum`](https://prove2.me/theorems/27178f99-4152-4a50-8019-f02f8e023497).
--
--   [Source excerpt, lines 96–105](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean#L96-L105) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean#L94-L211 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossOrthogonalityDirectCross`, declaration `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_crossSum_sq`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityDirectCross.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}

lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_crossSum_sq_readable (W : MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) :
    Integrable (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2) P
    ∧ ∫ ω, (∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2 ∂P
      = m * h ^ 2 := by sorry
