-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_marked_line_czero_compactness_bp240
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:45:25.966881+00:00
-- url     : https://prove2.me/theorems/72161e3e-45c8-4f06-978c-4034476ac623
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness` of [lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter MeasureTheory`, `open HolderCompletion`, `open scoped BoundedContinuousFunction`):
--
--   ```lean
--   theorem exact_marked_line_czero_compactness_bp240 {J : Phase n → End n}
--       (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
--       (hJc : HasCompactSupport (fun x => J x-standardJ n))
--       {S T : ℝ} (hST : S<T) (hT : T<1)
--       (hout : ∀ x,S < capacity x →J x=standardJ n)
--       {p q : Phase n} {t : ℕ → ℝ} (ht : ∀ j,t j∈Icc (0:ℝ) 1)
--       {u : ℕ → ℂ → Phase n} (hu : ∀ j,AffineLineCurve (lineHomotopy J (t j)) p q (u j)) :
--       ∃ v : C(ℂ,Phase n),v 0=p ∧ v 1=q ∧ ∃ φ : ℕ → ℕ,StrictMono φ ∧
--         ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn (fun j => u (φ j)) v atTop K
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy` and `OAI.HigherDimensionalBallPacking.Rigidity.standardJ` (definitions bundle `OAIQ240Bp000` of this split); `OAI.HigherDimensionalBallPacking.Phase` and `OAI.HigherDimensionalBallPacking.capacity` (the published bundle `Def_BallPacking`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_zeroSet_compact_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Compactness/MarkedCurves.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness)

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open HolderCompletion
open scoped BoundedContinuousFunction
variable {n : ℕ}

theorem exact_marked_line_czero_compactness_bp240 {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} {t : ℕ → ℝ} (ht : ∀ j,t j∈Icc (0:ℝ) 1)
    {u : ℕ → ℂ → Phase n} (hu : ∀ j,AffineLineCurve (lineHomotopy J (t j)) p q (u j)) :
    ∃ v : C(ℂ,Phase n),v 0=p ∧ v 1=q ∧ ∃ φ : ℕ → ℕ,StrictMono φ ∧
      ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn (fun j => u (φ j)) v atTop K := by
  sorry

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end
