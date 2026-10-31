-- Prove2me | Theorems.Thm_OAI_GeneralMahler_ProjField_budget
-- name    : OAI.GeneralMahler.ProjField.budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T00:39:36.172709+00:00
-- url     : https://prove2.me/theorems/25ce29f9-cd6d-4bc7-a3c2-b31878893b1e
-- title:
--   OAI.GeneralMahler.ProjField.budget: intermediate lemma from OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GeneralMahler.general_mahler`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mahler Conjecture for General Convex Bodies (result family 087)*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GeneralMahler.ProjField.budget` of [lean/OAI/Geometry/Convex/GeneralMahler/Budget/Eq23.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Budget/Eq23.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GeneralMahler.ProjField`, with `open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric`, `open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval`, `open HMode Profile Layers Seg Roots`):
--
--   ```lean
--   theorem budget (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat)
--       (hs:LayerOK) (hh:q.avgA=0) :
--       q.scoreE T ≤ q.DelP T-q.JVec q.covMat+(80/100)*Hcomm q.Lmat T+
--         (18/10)*trN (T*T)-q.BB q.FL (fun u=> ww u-ww0 u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.GeneralMahler.Hcomm`, `OAI.GeneralMahler.Mat`, `OAI.GeneralMahler.Plane`, `OAI.GeneralMahler.ProjField`, `OAI.GeneralMahler.specBox`, `OAI.GeneralMahler.tmax`, `OAI.GeneralMahler.tmin`, `OAI.GeneralMahler.trN`, `OAI.GeneralMahler.Profile.LayerOK`, `OAI.GeneralMahler.Profile.ww`, `OAI.GeneralMahler.Profile.ww0`, `OAI.GeneralMahler.ProjField.avgA` and `OAI.GeneralMahler.ProjField.covMat` (definitions bundle `OAIQ026G000` of this split); `OAI.GeneralMahler.ProjField.BB`, `OAI.GeneralMahler.ProjField.DelP`, `OAI.GeneralMahler.ProjField.FL`, `OAI.GeneralMahler.ProjField.JVec`, `OAI.GeneralMahler.ProjField.Lmat` and `OAI.GeneralMahler.ProjField.scoreE` (definitions bundle `OAIQ026G002` of this split).
--
--   **Used by.** The proof of `OAI.GeneralMahler.ProjField.C_bound` of this split imports it.
-- source:
--   OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087), OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Budget/Eq23.lean (declaration OAI.GeneralMahler.ProjField.budget)

import Mathlib
import Definitions.Def_OAIQ026G002

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.GeneralMahler.Body.instSetLikeRn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (T:Mat m)

theorem budget (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat)
    (hs:LayerOK) (hh:q.avgA=0) :
    q.scoreE T ≤ q.DelP T-q.JVec q.covMat+(80/100)*Hcomm q.Lmat T+
      (18/10)*trN (T*T)-q.BB q.FL (fun u=> ww u-ww0 u) := by
  sorry
end ProjField
end GeneralMahler

end

end OAI
end
