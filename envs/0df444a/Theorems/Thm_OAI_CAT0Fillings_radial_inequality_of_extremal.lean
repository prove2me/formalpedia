-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_radial_inequality_of_extremal
-- name    : OAI.CAT0Fillings.radial_inequality_of_extremal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:53:38.810903+00:00
-- url     : https://prove2.me/theorems/1d4a03a7-3cd6-4e0e-9cee-bd7363d5baf1
-- title:
--   OAI.CAT0Fillings.radial_inequality_of_extremal: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.radial_inequality_of_extremal` of [lean/OAI/Geometry/CAT0Fillings/Radial/ClosedInequality.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Radial/ClosedInequality.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings`, with `open Set Filter MeasureTheory`, `open scoped Topology NNReal`, `open CurrentOperations Foundations`):
--
--   ```lean
--   theorem radial_inequality_of_extremal (hX : IsCAT0 X) {k : ℕ}
--       {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
--       (q : ChartGeometry hT.1) {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p)
--       (hm : 0 < mass T)
--       (hext : ∀ B : Functional X (k+1), IsIntegral (k+1) B → boundarySucc B = 0 →
--         c*((mass T)^p-(mass B)^p) ≤ fillingVolume (T-B))
--       (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
--       (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
--       c*p*(mass T)^(p-1)*q.radialVariation o g ≤ q.sweptMass o g
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.ChartGeometry` (definitions bundle `OAIQ29C0000` of this split); `OAI.CAT0Fillings.fillingVolume`, `OAI.CAT0Fillings.ChartGeometry.radialVariation` and `OAI.CAT0Fillings.ChartGeometry.sweptMass` (definitions bundle `OAIQ29C0002` of this split); `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IntegerRectifiable`, `OAI.CAT0Fillings.IsCAT0`, `OAI.CAT0Fillings.IsIntegral`, `OAI.CAT0Fillings.IsMetricCurrent`, `OAI.CAT0Fillings.boundarySucc` and `OAI.CAT0Fillings.mass` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proofs of `OAI.CAT0Fillings.fillingVolume_le_two` and `OAI.CAT0Fillings.normalized_extremal_contradiction` of this split import it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Radial/ClosedInequality.lean (declaration OAI.CAT0Fillings.radial_inequality_of_extremal)

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

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings
open CurrentOperations Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem radial_inequality_of_extremal (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (q : ChartGeometry hT.1) {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hm : 0 < mass T)
    (hext : ∀ B : Functional X (k+1), IsIntegral (k+1) B → boundarySucc B = 0 →
      c*((mass T)^p-(mass B)^p) ≤ fillingVolume (T-B))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    c*p*(mass T)^(p-1)*q.radialVariation o g ≤ q.sweptMass o g := by
  sorry

end CAT0Fillings
end

end OAI
end
