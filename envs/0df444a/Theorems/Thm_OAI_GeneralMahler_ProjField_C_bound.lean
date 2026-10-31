-- Prove2me | Theorems.Thm_OAI_GeneralMahler_ProjField_C_bound
-- name    : OAI.GeneralMahler.ProjField.C_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T00:38:55.219472+00:00
-- url     : https://prove2.me/theorems/05cde5bf-12e5-4bac-a9e5-edeb84287679
-- title:
--   OAI.GeneralMahler.ProjField.C_bound: intermediate lemma from OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GeneralMahler.general_mahler`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mahler Conjecture for General Convex Bodies (result family 087)*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GeneralMahler.ProjField.C_bound` of [lean/OAI/Geometry/Convex/GeneralMahler/Rigid/Rays.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Rigid/Rays.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GeneralMahler.ProjField`, with `open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module`, `open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator`, `open Profile Segment`):
--
--   ```lean
--   theorem C_bound (q:ProjField m) (T:Mat m) (h:Balanced q T) (hc:UpdatesOK Cp Kp)
--       (hh:LayerOK) (hi:SegmentOK):
--       1 ≤ chi q.C q.V*chi q.D q.U ∧ (chi q.C q.V*chi q.D q.U=1 →
--         IsLinearOrthant m q.C)
--   ```
--
--   **Definitions.** The statement is written with `OAI.GeneralMahler.IsLinearOrthant`, `OAI.GeneralMahler.Mat`, `OAI.GeneralMahler.ProjField`, `OAI.GeneralMahler.UpdatesOK`, `OAI.GeneralMahler.chi`, `OAI.GeneralMahler.Profile.Cp`, `OAI.GeneralMahler.Profile.Kp`, `OAI.GeneralMahler.Profile.LayerOK`, `OAI.GeneralMahler.ProjField.D` and `OAI.GeneralMahler.Segment.SegmentOK` (definitions bundle `OAIQ026G000` of this split); `OAI.GeneralMahler.ProjField.Balanced` (definitions bundle `OAIQ026G002` of this split); `OAI.GeneralMahler.Rn` (the published bundle `Def_GeneralMahler`).
--
--   **Used by.** The proof of `OAI.GeneralMahler.general_mahler` of this split imports it.
-- source:
--   OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087), OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Rigid/Rays.lean (declaration OAI.GeneralMahler.ProjField.C_bound)

import Mathlib
import Definitions.Def_GeneralMahler
import Definitions.Def_OAIQ026G002

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Profile Segment
variable {m:ℕ}

namespace ProjField
variable [NeZero m]

theorem C_bound (q:ProjField m) (T:Mat m) (h:Balanced q T) (hc:UpdatesOK Cp Kp)
    (hh:LayerOK) (hi:SegmentOK):
    1 ≤ chi q.C q.V*chi q.D q.U ∧ (chi q.C q.V*chi q.D q.U=1 →
      IsLinearOrthant m q.C) := by
  sorry
end ProjField
end GeneralMahler

end

end OAI
end
