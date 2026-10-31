-- Prove2me | Theorems.Thm_OAI_GeneralMahler_ProjField_entropy_decomp
-- name    : OAI.GeneralMahler.ProjField.entropy_decomp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T00:38:23.360114+00:00
-- url     : https://prove2.me/theorems/8ab3fed3-0c3f-4bf8-8b17-332fa65c8e9e
-- title:
--   OAI.GeneralMahler.ProjField.entropy_decomp: intermediate lemma from OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GeneralMahler.general_mahler`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mahler Conjecture for General Convex Bodies (result family 087)*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GeneralMahler.ProjField.entropy_decomp` of [lean/OAI/Geometry/Convex/GeneralMahler/Eq18.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Eq18.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GeneralMahler.ProjField`, with `open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric`, `open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval`, `open Profile Layers HMode`):
--
--   ```lean
--   theorem entropy_decomp {T:Mat m} (he:1+T=q.covMat) (h:LayerOK) :
--       q.delt d-etw T (q.Hmat v) ≤
--         q.DelP T + q.sigma FF-q.DVec-q.JVec q.covMat-Pt T q.RR (q.FL.eval (deriv v))-
--           q.LLw q.FL 1 HH -
--           q.LLw q.FL T (fun u=> HH u+deriv (deriv v) u.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.GeneralMahler.Mat`, `OAI.GeneralMahler.Plane`, `OAI.GeneralMahler.ProjField`, `OAI.GeneralMahler.FieldMat.eval`, `OAI.GeneralMahler.Profile.FF`, `OAI.GeneralMahler.Profile.HH`, `OAI.GeneralMahler.Profile.LayerOK`, `OAI.GeneralMahler.Profile.d`, `OAI.GeneralMahler.Profile.v`, `OAI.GeneralMahler.ProjField.Hmat` and `OAI.GeneralMahler.ProjField.covMat` (definitions bundle `OAIQ026G000` of this split); `OAI.GeneralMahler.Pt`, `OAI.GeneralMahler.etw`, `OAI.GeneralMahler.ProjField.DVec`, `OAI.GeneralMahler.ProjField.DelP`, `OAI.GeneralMahler.ProjField.FL`, `OAI.GeneralMahler.ProjField.JVec`, `OAI.GeneralMahler.ProjField.LLw`, `OAI.GeneralMahler.ProjField.RR`, `OAI.GeneralMahler.ProjField.delt` and `OAI.GeneralMahler.ProjField.sigma` (definitions bundle `OAIQ026G002` of this split).
--
--   **Used by.** The proof of `OAI.GeneralMahler.ProjField.budget` of this split imports it.
-- source:
--   OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087), OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Convex/GeneralMahler/Eq18.lean (declaration OAI.GeneralMahler.ProjField.entropy_decomp)

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
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m)

theorem entropy_decomp {T:Mat m} (he:1+T=q.covMat) (h:LayerOK) :
    q.delt d-etw T (q.Hmat v) ≤
      q.DelP T + q.sigma FF-q.DVec-q.JVec q.covMat-Pt T q.RR (q.FL.eval (deriv v))-
        q.LLw q.FL 1 HH -
        q.LLw q.FL T (fun u=> HH u+deriv (deriv v) u.2) := by
  sorry
end ProjField
end GeneralMahler

end

end OAI
end
