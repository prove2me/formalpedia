-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_sq_mul_and_le_readable
-- name    : LevyStochCalc.Brownian.Ito.integrable_sq_mul_and_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:29.580982+00:00
-- url     : https://prove2.me/theorems/9194c79a-683c-4a17-8bf7-6d933792ea69
-- title:
--   Second Moment of a Product from Fourth Moments
-- statement:
--   This is an integrability and moment bound for the square of a product.
--
--   Let $A,B:\Omega\to\mathbb R$ be measurable functions on a measure space $(\Omega,P)$. Assume $A^4$ and $B^4$ are integrable. Then $(AB)^2$ is integrable and
--   $$
--   \int (AB)^2\,dP
--   \le\frac{1}{2}\left(\int A^4\,dP+\int B^4\,dP\right).
--   $$
--
--   The lemma is a general-purpose product estimate used to control squares of cross-increment terms; no probability-measure assumption is required.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_sq_mul_and_le {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
--       (hA4 : Integrable (fun ω => A ω ^ 4) P) (hB4 : Integrable (fun ω => B ω ^ 4) P) :
--       Integrable (fun ω => (A ω * B ω) ^ 2) P
--         ∧ ∫ ω, (A ω * B ω) ^ 2 ∂P ≤ (∫ ω, A ω ^ 4 ∂P + ∫ ω, B ω ^ 4 ∂P) / 2
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/CrossVariationSum`](https://prove2.me/theorems/a1ff2b05-5818-415f-a2f2-029a029a1d6c).
--
--   Next: [`integral_sq_weighted_crossSum_le`](https://prove2.me/theorems/5d328781-1a8c-43bf-be55-0a5141e07939).
--
--   [Source excerpt, lines 44–47](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/CrossVariationSum.lean#L44-L47) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/CrossVariationSum.lean#L41-L59 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.CrossVariationSum`, declaration `LevyStochCalc.Brownian.Ito.integrable_sq_mul_and_le`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossVariationSum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossVariationSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
omit [IsProbabilityMeasure P]

theorem LevyStochCalc.Brownian.Ito.integrable_sq_mul_and_le_readable {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA4 : Integrable (fun ω => A ω ^ 4) P) (hB4 : Integrable (fun ω => B ω ^ 4) P) :
    Integrable (fun ω => (A ω * B ω) ^ 2) P
      ∧ ∫ ω, (A ω * B ω) ^ 2 ∂P ≤ (∫ ω, A ω ^ 4 ∂P + ∫ ω, B ω ^ 4 ∂P) / 2 := by sorry
