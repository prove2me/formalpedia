-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_line_local_energy_of_slope_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.exact_line_local_energy_of_slope_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:52:59.747131+00:00
-- url     : https://prove2.me/theorems/7def7e36-51d8-40d6-9871-f1588cbb80ae
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.exact_line_local_energy_of_slope_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.exact_line_local_energy_of_slope` of [lean/OAI/Geometry/BallPacking/Campanato/TranslatedSquare.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Campanato/TranslatedSquare.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter MeasureTheory`):
--
--   ```lean
--   lemma exact_line_local_energy_of_slope_bp240 {J : Phase n → End n}
--       (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
--       (hJc : HasCompactSupport (fun x => J x-standardJ n))
--       {S T : ℝ} (hST : S<T) (hT : T<1)
--       (hout : ∀ x, S < capacity x → J x=standardJ n) :
--       ∃ C M θ : ℝ,0<C ∧ 0≤M ∧ 0<θ ∧ θ<1 ∧
--         ∀ t∈Icc (0:ℝ) 1,∀ (p q : Phase n) (u : ℂ → Phase n),
--           AffineLineCurve (lineHomotopy J t) p q u →
--           ∀ a : Phase n,Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
--           ∀ (c : ℂ) (k : ℕ),radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤
--             (C+M*stdDot n a a)*θ^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy`, `OAI.HigherDimensionalBallPacking.Rigidity.standardJ` and `OAI.HigherDimensionalBallPacking.Rigidity.stdDot` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.centeredCurve` (definitions bundle `OAIQ240Bp017` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.radialCurveEnergy` (definitions bundle `OAIQ240Bp018` of this split); `OAI.HigherDimensionalBallPacking.Phase` and `OAI.HigherDimensionalBallPacking.capacity` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proofs of `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_gradient_bound_bp240`, `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_uniform_defect_support_bp240` and `OAI.HigherDimensionalBallPacking.Rigidity.exact_normalized_line_energy_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Campanato/TranslatedSquare.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.exact_line_local_energy_of_slope)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp017
import Definitions.Def_OAIQ240Bp018

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ}

lemma exact_line_local_energy_of_slope_bp240 {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S < capacity x → J x=standardJ n) :
    ∃ C M θ : ℝ,0<C ∧ 0≤M ∧ 0<θ ∧ θ<1 ∧
      ∀ t∈Icc (0:ℝ) 1,∀ (p q : Phase n) (u : ℂ → Phase n),
        AffineLineCurve (lineHomotopy J t) p q u →
        ∀ a : Phase n,Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
        ∀ (c : ℂ) (k : ℕ),radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤
          (C+M*stdDot n a a)*θ^k := by
  sorry

end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end
