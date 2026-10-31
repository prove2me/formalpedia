-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_normalized_extremal_contradiction
-- name    : OAI.CAT0Fillings.normalized_extremal_contradiction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:53:17.459477+00:00
-- url     : https://prove2.me/theorems/ee1efead-0440-4850-8e48-1dff24c14ffd
-- title:
--   OAI.CAT0Fillings.normalized_extremal_contradiction: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.normalized_extremal_contradiction` of [lean/OAI/Geometry/CAT0Fillings/Euler/NormalizedContradiction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Euler/NormalizedContradiction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings`, with `open Set Filter MeasureTheory Metric`, `open scoped Topology NNReal ENNReal`, `open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev`):
--
--   ```lean
--   theorem normalized_extremal_contradiction {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
--       {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
--       (hm : 0 < mass T) (hms : mass T < sphereArea (k+2))
--       {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
--       (hnorm : d*r*(mass T)^(r-1) = 1/(k+2:ℝ))
--       (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
--         ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
--           mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
--       (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
--         d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B)) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.fillingVolume` (definitions bundle `OAIQ29C0002` of this split); `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IsCAT0`, `OAI.CAT0Fillings.IsIntegral`, `OAI.CAT0Fillings.boundarySucc`, `OAI.CAT0Fillings.fillingCoefficient`, `OAI.CAT0Fillings.fillingPower`, `OAI.CAT0Fillings.mass` and `OAI.CAT0Fillings.sphereArea` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proof of `OAI.CAT0Fillings.sharp_integral_filling` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Euler/NormalizedContradiction.lean (declaration OAI.CAT0Fillings.normalized_extremal_contradiction)

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
theorem normalized_extremal_contradiction {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (hms : mass T < sphereArea (k+2))
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hnorm : d*r*(mass T)^(r-1) = 1/(k+2:ℝ))
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B)) : False := by
  sorry
end CAT0Fillings
end

end OAI
end
