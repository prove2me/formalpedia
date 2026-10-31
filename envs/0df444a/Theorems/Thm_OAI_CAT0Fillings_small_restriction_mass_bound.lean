-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_small_restriction_mass_bound
-- name    : OAI.CAT0Fillings.small_restriction_mass_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:54:08.597354+00:00
-- url     : https://prove2.me/theorems/470b267c-e0be-4043-894f-a1149cd691c1
-- title:
--   OAI.CAT0Fillings.small_restriction_mass_bound: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.small_restriction_mass_bound` of [lean/OAI/Geometry/CAT0Fillings/Isoperimetry/SmallSets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Isoperimetry/SmallSets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings`, with `open Set Filter MeasureTheory Metric`, `open scoped Topology NNReal`, `open Foundations MassMeasure BorelRestriction CurrentOperations`):
--
--   ```lean
--   theorem small_restriction_mass_bound (hX : IsCAT0 X) {k : ℕ} {c p d q : ℝ}
--       (hc : 0 ≤ c) (hp : 1 < p) (hd : 0 < d) (hq : 1 < q)
--       (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
--         ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
--           mass R ≤ c*(mass P)^p)
--       {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
--       (hm : 0 < mass T)
--       (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
--         d*((mass T)^q-(mass B)^q) ≤ fillingVolume (T-B))
--       {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
--       ∃ δ : ℝ, δ ∈ Ioo 0 (mass T/2) ∧ ∀ E : Set X, ∀ _hE : MeasurableSet E,
--         IsIntegral (k+2) (restrictCurrent hT.1 E) → mass (restrictCurrent hT.1 E) ≤ δ →
--         (1-η)*mass (restrictCurrent hT.1 E) ≤
--           c*(mass (boundarySucc (restrictCurrent hT.1 E)))^p
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.BorelRestriction.restrictCurrent` (definitions bundle `OAIQ29C0000` of this split); `OAI.CAT0Fillings.fillingVolume` (definitions bundle `OAIQ29C0002` of this split); `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IntegerRectifiable`, `OAI.CAT0Fillings.IsCAT0`, `OAI.CAT0Fillings.IsIntegral`, `OAI.CAT0Fillings.IsMetricCurrent`, `OAI.CAT0Fillings.boundarySucc` and `OAI.CAT0Fillings.mass` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proofs of `OAI.CAT0Fillings.extremal_closed_sobolev` and `OAI.CAT0Fillings.extremal_critical_minimizer` of this split import it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Isoperimetry/SmallSets.lean (declaration OAI.CAT0Fillings.small_restriction_mass_bound)

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002

section

attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations MassMeasure BorelRestriction CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem small_restriction_mass_bound (hX : IsCAT0 X) {k : ℕ} {c p d q : ℝ}
    (hc : 0 ≤ c) (hp : 1 < p) (hd : 0 < d) (hq : 1 < q)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ c*(mass P)^p)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T)
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^q-(mass B)^q) ≤ fillingVolume (T-B))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ δ : ℝ, δ ∈ Ioo 0 (mass T/2) ∧ ∀ E : Set X, ∀ _hE : MeasurableSet E,
      IsIntegral (k+2) (restrictCurrent hT.1 E) → mass (restrictCurrent hT.1 E) ≤ δ →
      (1-η)*mass (restrictCurrent hT.1 E) ≤
        c*(mass (boundarySucc (restrictCurrent hT.1 E)))^p := by
  sorry

end CAT0Fillings
end

end OAI
end
