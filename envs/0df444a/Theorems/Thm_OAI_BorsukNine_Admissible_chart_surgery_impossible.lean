-- Prove2me | Theorems.Thm_OAI_BorsukNine_Admissible_chart_surgery_impossible
-- name    : OAI.BorsukNine.Admissible.chart_surgery_impossible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:41:04.21705+00:00
-- url     : https://prove2.me/theorems/e70d9de8-360a-425d-87b6-fae0d3b423d8
-- title:
--   OAI.BorsukNine.Admissible.chart_surgery_impossible: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.Admissible.chart_surgery_impossible` of [lean/OAI/Geometry/Borsuk/Projectors/ChartSurgery.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Projectors/ChartSurgery.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator`, `open Set`):
--
--   ```lean
--   lemma Admissible.chart_surgery_impossible {f : E → ι → ℝ} (hf : Admissible f)
--       (hdim : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
--       {I : Finset ι} (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
--       (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
--       {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
--       {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
--       (c : κ → E) (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
--       (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
--         (interior (signChamber (activeVectors f I) (c j)))))
--       (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
--       {ε : ℝ} (hε : 0 < ε) (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι))
--       (hg : ∀ j, Continuous (g j)) (hgs : ∀ j, ∀ Q ∈ matrixFibre (c j), ∑ i, g j Q i = 1)
--       (hge : ∀ j, ∀ Q ∈ matrixFibre (c j), ‖g j Q - negativeCoordinates f I Q‖ < ε)
--       (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hz : ∀ i, ε < z i) (hzs : ∑ i, z i = 1)
--       (hgm : ∀ j, ∀ Q ∈ matrixFibre (c j), g j Q ≠ z) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.Admissible`, `OAI.BorsukNine.UpperTriangle`, `OAI.BorsukNine.activeVectors`, `OAI.BorsukNine.commonPositiveCone`, `OAI.BorsukNine.matrixFibre`, `OAI.BorsukNine.negativeCoordinates`, `OAI.BorsukNine.orientedLevel`, `OAI.BorsukNine.positiveSupport` and `OAI.BorsukNine.signChamber` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proofs of `OAI.BorsukNine.Admissible.face_extends_four` and `OAI.BorsukNine.Admissible.face_extends_three` of this split import it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Projectors/ChartSurgery.lean (declaration OAI.BorsukNine.Admissible.chart_surgery_impossible)

import Mathlib
import Definitions.Def_OAIQ058B000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section ChartSurgery
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι

lemma Admissible.chart_surgery_impossible {f : E → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    {I : Finset ι} (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    (c : κ → E) (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    {ε : ℝ} (hε : 0 < ε) (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι))
    (hg : ∀ j, Continuous (g j)) (hgs : ∀ j, ∀ Q ∈ matrixFibre (c j), ∑ i, g j Q i = 1)
    (hge : ∀ j, ∀ Q ∈ matrixFibre (c j), ‖g j Q - negativeCoordinates f I Q‖ < ε)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hz : ∀ i, ε < z i) (hzs : ∑ i, z i = 1)
    (hgm : ∀ j, ∀ Q ∈ matrixFibre (c j), g j Q ≠ z) : False := by
  sorry

end ChartSurgery
end BorsukNine

end OAI
end
