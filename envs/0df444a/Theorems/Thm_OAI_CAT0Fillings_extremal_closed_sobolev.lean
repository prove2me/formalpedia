-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_extremal_closed_sobolev
-- name    : OAI.CAT0Fillings.extremal_closed_sobolev
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:53:06.17278+00:00
-- url     : https://prove2.me/theorems/2eb727af-7b54-4a7f-84cf-b154358980d0
-- title:
--   OAI.CAT0Fillings.extremal_closed_sobolev: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.extremal_closed_sobolev` of [lean/OAI/Geometry/CAT0Fillings/Sobolev/Compact.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Sobolev/Compact.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings`, with `open Set Filter MeasureTheory`, `open scoped Topology NNReal ENNReal`, `open Set Filter MeasureTheory MassMeasure Rearrangement RadialSobolev`, `open scoped Topology NNReal ENNReal`):
--
--   ```lean
--   theorem extremal_closed_sobolev {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
--       {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
--       (hm : 0 < mass T) (q : ChartGeometry hT.1) {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
--       (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
--         ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
--           mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
--       (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
--         d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B))
--       {ε : ℝ} (hε : 0 < ε) (hεS : ε < (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))) :
--       ∃ C ≥ (0:ℝ), ∀ P : q.Sobolev,
--         MemLp (q.inclusion P) (ENNReal.ofReal (sobolevP (k+2))) (currentMassMeasure hT.1) ∧
--         ((k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))-ε)*
--           lpNorm (q.inclusion P) (ENNReal.ofReal (sobolevP (k+2))) (currentMassMeasure hT.1)^2 ≤
--         4/((k+2:ℝ)-2)*‖q.closedGradient P‖^2 + C*‖q.inclusion P‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.ChartGeometry`, `OAI.CAT0Fillings.ChartGeometry.GraphAmbient`, `OAI.CAT0Fillings.ChartGeometry.Sobolev`, `OAI.CAT0Fillings.ChartGeometry.atlasMeasure`, `OAI.CAT0Fillings.ChartGeometry.closedGradient`, `OAI.CAT0Fillings.ChartGeometry.inclusion` and `OAI.CAT0Fillings.MassMeasure.currentMassMeasure` (definitions bundle `OAIQ29C0000` of this split); `OAI.CAT0Fillings.RadialSobolev.sobolevP` (definitions bundle `OAIQ29C0001` of this split); `OAI.CAT0Fillings.fillingVolume` (definitions bundle `OAIQ29C0002` of this split); `OAI.CAT0Fillings.Euc`, `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IntegerRectifiable`, `OAI.CAT0Fillings.IsCAT0`, `OAI.CAT0Fillings.IsIntegral`, `OAI.CAT0Fillings.IsMetricCurrent`, `OAI.CAT0Fillings.boundarySucc`, `OAI.CAT0Fillings.fillingCoefficient`, `OAI.CAT0Fillings.fillingPower`, `OAI.CAT0Fillings.mass` and `OAI.CAT0Fillings.sphereArea` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proofs of `OAI.CAT0Fillings.extremal_critical_minimizer`, `OAI.CAT0Fillings.extremal_euler_powers` and `OAI.CAT0Fillings.normalized_extremal_contradiction` of this split import it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Sobolev/Compact.lean (declaration OAI.CAT0Fillings.extremal_closed_sobolev)

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002

section

attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open Set Filter MeasureTheory MassMeasure Rearrangement RadialSobolev
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem extremal_closed_sobolev {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (q : ChartGeometry hT.1) {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B))
    {ε : ℝ} (hε : 0 < ε) (hεS : ε < (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))) :
    ∃ C ≥ (0:ℝ), ∀ P : q.Sobolev,
      MemLp (q.inclusion P) (ENNReal.ofReal (sobolevP (k+2))) (currentMassMeasure hT.1) ∧
      ((k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))-ε)*
        lpNorm (q.inclusion P) (ENNReal.ofReal (sobolevP (k+2))) (currentMassMeasure hT.1)^2 ≤
      4/((k+2:ℝ)-2)*‖q.closedGradient P‖^2 + C*‖q.inclusion P‖^2 := by
  sorry

end CAT0Fillings
end

end OAI
end
