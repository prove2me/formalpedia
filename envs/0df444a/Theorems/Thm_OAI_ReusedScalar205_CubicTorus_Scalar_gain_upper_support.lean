-- Prove2me | Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_gain_upper_support
-- name    : OAI.ReusedScalar205.CubicTorus.Scalar.gain_upper_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:50:21.211982+00:00
-- url     : https://prove2.me/theorems/b702f754-4067-4ffc-9c13-0f928b4b4e15
-- title:
--   OAI.ReusedScalar205.CubicTorus.Scalar.gain_upper_support: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ReusedScalar205.CubicTorus.Scalar.gain_upper_support` of [lean/OAI/Geometry/CubicTorus/Profiles/GainBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/GainBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ReusedScalar205.CubicTorus.Scalar`, with `open Set MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory`, `open scoped Interval`, `open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape _root_.OAI.ReusedScalar205.CubicTorus.Reduction`, `open scoped Topology`):
--
--   ```lean
--   lemma gain_upper_support {h : ℝ} (hh : h ∈ Ioo (51 / 50 : ℝ) (81 / 50 : ℝ)) :
--       ∃ F : ℝ → ℝ, UpperSupport gain F h ∧ deriv (deriv F) h ≤ 2 / 5
--   ```
--
--   **Definitions.** The statement is written with `OAI.ReusedScalar205.CubicTorus.Reduction.UpperSupport` (definitions bundle `OAIQ079A001` of this split); `OAI.ReusedScalar205.CubicTorus.Scalar.gain` (definitions bundle `OAIQ079A003` of this split).
--
--   **Used by.** The proof of `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.combined_positive` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/GainBounds.lean (declaration OAI.ReusedScalar205.CubicTorus.Scalar.gain_upper_support)

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

lemma gain_upper_support {h : ℝ} (hh : h ∈ Ioo (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    ∃ F : ℝ → ℝ, UpperSupport gain F h ∧ deriv (deriv F) h ≤ 2 / 5 := by
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
