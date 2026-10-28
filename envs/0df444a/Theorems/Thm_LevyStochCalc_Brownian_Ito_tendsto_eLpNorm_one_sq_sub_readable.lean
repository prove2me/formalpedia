-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_eLpNorm_one_sq_sub_readable
-- name    : LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:23.980875+00:00
-- url     : https://prove2.me/theorems/f09a6b4b-92fc-4d7f-afe6-745f7f468f5b
-- title:
--   L¹ Convergence of Squares from L² Convergence
-- statement:
--   Let $a_n:\Omega\to\mathbb R$ be a filter-indexed family and let $b:\Omega\to\mathbb R$. Assume every $a_n$ and $b$ is almost-everywhere measurable, $\|b\|_{L^2(\mu)}\ne\infty$, and
--
--   $$\|a_n-b\|_{L^2(\mu)}\longrightarrow 0$$
--
--   along a filter $l$. Then
--
--   $$\left\|a_n^2-b^2\right\|_{L^1(\mu)}\longrightarrow 0$$
--
--   along $l$. The norms are the extended $L^p$ norms, with the stated non-top hypothesis on the limiting $L^2$ norm.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma tendsto_eLpNorm_one_sq_sub
--       {μ : MeasureTheory.Measure Ω} {ι : Type*} {l : Filter ι} {a : ι → Ω → ℝ} {b : Ω → ℝ}
--       (ha : ∀ n, AEMeasurable (a n) μ) (hb : AEMeasurable b μ)
--       (hbfin : MeasureTheory.eLpNorm b 2 μ ≠ ⊤)
--       (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ)
--         l (nhds 0)) :
--       Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ)
--         l (nhds 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionConvergence`](https://prove2.me/theorems/7052eb64-0ceb-40e0-81f7-f59b0f13c887).
--
--   Supporting theorems: [`eLpNorm_one_mul_le`](https://prove2.me/theorems/11203bf2-6375-4c0c-9036-2bedd1d686fd).
--
--   Previous: [`eLpNorm_one_mul_le`](https://prove2.me/theorems/11203bf2-6375-4c0c-9036-2bedd1d686fd) · Next: [`condExp_sq_increment_of_martingale`](https://prove2.me/theorems/9248f0a4-cf9c-4337-bd6c-ca5656254c6a).
--
--   [Source excerpt, lines 134–141](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean#L134-L141) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean#L130-L173 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionConvergence`, declaration `LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub_readable
    {μ : MeasureTheory.Measure Ω} {ι : Type*} {l : Filter ι} {a : ι → Ω → ℝ} {b : Ω → ℝ}
    (ha : ∀ n, AEMeasurable (a n) μ) (hb : AEMeasurable b μ)
    (hbfin : MeasureTheory.eLpNorm b 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ)
      l (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ)
      l (nhds 0) := by sorry
