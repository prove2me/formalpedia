-- Prove2me | Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_twoChordBaseline_le_of_range
-- name    : OAI.ReusedScalar205.CubicTorus.Scalar.twoChordBaseline_le_of_range
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:50:44.892268+00:00
-- url     : https://prove2.me/theorems/a6bc7b83-d752-49cf-86db-836edd00f05d
-- title:
--   OAI.ReusedScalar205.CubicTorus.Scalar.twoChordBaseline_le_of_range: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ReusedScalar205.CubicTorus.Scalar.twoChordBaseline_le_of_range` of [lean/OAI/Geometry/CubicTorus/Profiles/GainBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/GainBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ReusedScalar205.CubicTorus.Scalar`, with `open Set MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory`, `open scoped Interval`, `open Set _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape`):
--
--   ```lean
--   lemma twoChordBaseline_le_of_range {h : ℝ} (hh : 0 < h) (hu : h ≤ 71 / 50) :
--       twoChordBaseline h ≤ baseline h
--   ```
--
--   **Definitions.** The statement is written with `OAI.ReusedScalar205.CubicTorus.Scalar.baseline` and `OAI.ReusedScalar205.CubicTorus.Scalar.twoChordBaseline` (definitions bundle `OAIQ079A003` of this split).
--
--   **Used by.** The proofs of `OAI.CubicTorus.critical_nesting_contradiction`, `OAI.CubicTorus.nesting_scalar_contradiction`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_64`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_84`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.baseline_lower_92`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_102`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_106`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_110`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_114`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_118`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_122`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_126`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_130`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_134`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_138`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_142`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_64_74`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_74_84` and `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.positive_98_102` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/GainBounds.lean (declaration OAI.ReusedScalar205.CubicTorus.Scalar.twoChordBaseline_le_of_range)

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
open Set _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma twoChordBaseline_le_of_range {h : ℝ} (hh : 0 < h) (hu : h ≤ 71 / 50) :
    twoChordBaseline h ≤ baseline h := by
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
