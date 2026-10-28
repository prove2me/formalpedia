-- Prove2me | Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_Cert_combined_lower_138
-- name    : OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_138
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:44:35.591203+00:00
-- url     : https://prove2.me/theorems/a260aeb0-033e-4073-846a-1a42c2e3af46
-- title:
--   OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_138: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_138` of [lean/OAI/Geometry/CubicTorus/Profiles/GainEnclosure150.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/GainEnclosure150.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ReusedScalar205.CubicTorus.Scalar.Cert`, with `open Set MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory`, `open scoped Interval`, `open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape`):
--
--   ```lean
--   lemma combined_lower_138 : (507522239 / 500000000000 : ℝ) ≤ baseline (69 / 50 : ℝ) + gain (69 / 50 : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ReusedScalar205.CubicTorus.Scalar.baseline` and `OAI.ReusedScalar205.CubicTorus.Scalar.gain` (definitions bundle `OAIQ079A003` of this split).
--
--   **Used by.** The proof of `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_positive` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/GainEnclosure150.lean (declaration OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_lower_138)

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
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma combined_lower_138 : (507522239 / 500000000000 : ℝ) ≤ baseline (69 / 50 : ℝ) + gain (69 / 50 : ℝ) := by
  sorry

end CubicTorus.Scalar.Cert

end
end
end
end ReusedScalar205

end

end

end OAI
end
