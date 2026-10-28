-- Prove2me | Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_concaveOn_baseline_corrected
-- name    : OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:49:06.193247+00:00
-- url     : https://prove2.me/theorems/913bbe8d-0e97-485e-a1c4-d4793f63e136
-- title:
--   OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected` of [lean/OAI/Geometry/CubicTorus/Profiles/ProfileBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/ProfileBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ReusedScalar205.CubicTorus.Scalar`, with `open Set MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory`, `open scoped Interval`, `open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction`, `open scoped Topology`, `open MeasureTheory`):
--
--   ```lean
--   theorem concaveOn_baseline_corrected {a b : ℝ} (ha : 0 < a) :
--       ConcaveOn ℝ (Icc a b) (fun h ↦ baseline h - h ^ 2 / a ^ 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ReusedScalar205.CubicTorus.Scalar.baseline` (definitions bundle `OAIQ079A003` of this split).
--
--   **Used by.** The proofs of `OAI.CubicTorus.critical_baseline_positive`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_positive` and `OAI.ReusedScalar205.CubicTorus.Scalar.baseline_chord_lower` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/ProfileBounds.lean (declaration OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_baseline_corrected)

import Mathlib
import Definitions.Def_OAIQ079A003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction
open scoped Topology

open MeasureTheory

theorem concaveOn_baseline_corrected {a b : ℝ} (ha : 0 < a) :
    ConcaveOn ℝ (Icc a b) (fun h ↦ baseline h - h ^ 2 / a ^ 2) := by
  sorry

end CubicTorus.Scalar

end
end
end
end ReusedScalar205
end
end

end OAI
end
