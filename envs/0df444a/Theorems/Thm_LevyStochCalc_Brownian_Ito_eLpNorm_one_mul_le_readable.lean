-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_eLpNorm_one_mul_le_readable
-- name    : LevyStochCalc.Brownian.Ito.eLpNorm_one_mul_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:17.471271+00:00
-- url     : https://prove2.me/theorems/11203bf2-6375-4c0c-9036-2bedd1d686fd
-- title:
--   L² Product Bound in eLpNorm
-- statement:
--   Let $(\Omega,\mu)$ be a measure space and let $f,g:\Omega\to\mathbb R$ be almost-everywhere measurable. Then the extended $L^p$ norms satisfy
--
--   $$\|fg\|_{L^1(\mu)}\le \|f\|_{L^2(\mu)}\,\|g\|_{L^2(\mu)}.$$
--
--   Here each eLpNorm is an extended nonnegative value in $[0,\infty]$; no finiteness assumption is imposed. This is the Cauchy–Schwarz/Hölder estimate used to control products in $L^1$ from $L^2$ bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   lemma eLpNorm_one_mul_le {μ : MeasureTheory.Measure Ω} {f g : Ω → ℝ}
--       (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
--       MeasureTheory.eLpNorm (f * g) 1 μ
--         ≤ MeasureTheory.eLpNorm f 2 μ * MeasureTheory.eLpNorm g 2 μ
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoL2CompletionConvergence`](https://prove2.me/theorems/7052eb64-0ceb-40e0-81f7-f59b0f13c887).
--
--   Next: [`tendsto_eLpNorm_one_sq_sub`](https://prove2.me/theorems/f09a6b4b-92fc-4d7f-afe6-745f7f468f5b).
--
--   [Source excerpt, lines 112–115](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean#L112-L115) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean#L109-L128 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionConvergence`, declaration `LevyStochCalc.Brownian.Ito.eLpNorm_one_mul_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

lemma LevyStochCalc.Brownian.Ito.eLpNorm_one_mul_le_readable {μ : MeasureTheory.Measure Ω} {f g : Ω → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    MeasureTheory.eLpNorm (f * g) 1 μ
      ≤ MeasureTheory.eLpNorm f 2 μ * MeasureTheory.eLpNorm g 2 μ := by sorry
