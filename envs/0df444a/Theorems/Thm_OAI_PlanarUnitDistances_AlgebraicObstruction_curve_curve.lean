-- Prove2me | Theorems.Thm_OAI_PlanarUnitDistances_AlgebraicObstruction_curve_curve
-- name    : OAI.PlanarUnitDistances.AlgebraicObstruction.curve_curve
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T02:55:47.739134+00:00
-- url     : https://prove2.me/theorems/30edaa2b-fbe4-4070-ad7b-1d82e69eaa86
-- title:
--   OAI.PlanarUnitDistances.AlgebraicObstruction.curve_curve: intermediate lemma from OpenAI, A power saving for planar unit distances
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarUnitDistances.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A power saving for planar unit distances*, OpenAI Math Release, September 23, 2026, result family 167, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarUnitDistances.AlgebraicObstruction.curve_curve` of [lean/OAI/Geometry/UnitDistances/UnitDistances/Obstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances/UnitDistances/Obstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarUnitDistances.AlgebraicObstruction`, with `open Filter Polynomial UnitDistances.UltraField`, `open UnitDistances.ExactSmallHeightField UnitDistances.ExactHeightObstruction`, `open PowerGrowth BivariateMaps`):
--
--   ```lean
--   lemma curve_curve (hcurveA : DenseLoci.OnCurve U A id star)
--       (hcurveB : DenseLoci.OnCurve U B id star) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarUnitDistances.AlgebraicObstruction.Hypotheses`, `OAI.PlanarUnitDistances.DenseLoci.OnCurve`, `OAI.PlanarUnitDistances.GenericGrid.edges`, `OAI.PlanarUnitDistances.PowerGrowth.Lower` and `OAI.PlanarUnitDistances.PowerGrowth.Upper` (definitions bundle `OAIQ2Un000` of this split).
--
--   **Used by.** The proof of `OAI.PlanarUnitDistances.AlgebraicObstruction.no_rectangles` of this split imports it.
-- source:
--   OpenAI, A power saving for planar unit distances, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-unit-distances-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances/UnitDistances/Obstruction.lean (declaration OAI.PlanarUnitDistances.AlgebraicObstruction.curve_curve)

import Mathlib
import Definitions.Def_OAIQ2Un000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.AlgebraicObstruction
open Filter Polynomial UnitDistances.UltraField
open UnitDistances.ExactSmallHeightField UnitDistances.ExactHeightObstruction
open PowerGrowth BivariateMaps

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ)≤atTop) (t J : ℕ → ℝ)
  (ht : Tendsto t (U : Filter ℕ) atTop) (hJ : Tendsto J (U : Filter ℕ) atTop)
  (P A B : ℕ → Finset ℂ) (E : ℕ → ℂ → ℂ → Prop)
  (hsub : ∀ n,A n⊆P n ∧ B n⊆P n)
  (hA : Upper (U : Filter ℕ) t (fun n => (A n).card) 1)
  (hB : Upper (U : Filter ℕ) t (fun n => (B n).card) 1)
  (hAf : Lower (U : Filter ℕ) t (fun n => (A n).card) 1)
  (hBf : Lower (U : Filter ℕ) t (fun n => (B n).card) 1)
  (he : Lower (U : Filter ℕ) t
    (fun n => (GenericGrid.edges (fun n (a : A n) (b : B n) => E n a b) n).card) 2)
  (K : ℕ → Type) [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
  (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)
  (H : Hypotheses U t J P E K e ell)

include hU ht hJ hsub hA hB hAf hBf he H
lemma curve_curve (hcurveA : DenseLoci.OnCurve U A id star)
    (hcurveB : DenseLoci.OnCurve U B id star) : False := by
  sorry
end PlanarUnitDistances.AlgebraicObstruction

end OAI
end
