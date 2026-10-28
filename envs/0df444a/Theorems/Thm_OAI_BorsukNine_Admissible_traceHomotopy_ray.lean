-- Prove2me | Theorems.Thm_OAI_BorsukNine_Admissible_traceHomotopy_ray
-- name    : OAI.BorsukNine.Admissible.traceHomotopy_ray
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:43:58.609922+00:00
-- url     : https://prove2.me/theorems/eea502ea-a054-4a96-a350-2ca084f14389
-- title:
--   OAI.BorsukNine.Admissible.traceHomotopy_ray: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.Admissible.traceHomotopy_ray` of [lean/OAI/Geometry/Borsuk/MatrixGeometry/TraceHomotopy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/MatrixGeometry/TraceHomotopy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open scoped MatrixOrder Matrix.Norms.L2Operator`, `open SimplicialChains`):
--
--   ```lean
--   lemma Admissible.traceHomotopy_ray {f : EuclideanSpace ℝ ν → ι → ℝ} (_hf : Admissible f)
--       (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
--       (G : ℝ × traceSphere ν → Y)
--       (hG : ContinuousOn G (Set.Icc (0:ℝ) 1 ×ˢ Set.univ))
--       (hG0 : ∀ A : traceSphere ν, G (0,A) = WithLp.toLp 2 (signedExtension f A.val))
--       (hGz : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ A : traceSphere ν, G (t,A) ≠ 0)
--       {y : Y} (hy : y ≠ 0) :
--       ∃ A : traceSphere ν, ∃ t : ℝ, 0 < t ∧ G (1,A) = t • y
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.Admissible`, `OAI.BorsukNine.UpperTriangle`, `OAI.BorsukNine.signedExtension` and `OAI.BorsukNine.traceSphere` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proof of `OAI.BorsukNine.Admissible.chart_surgery_impossible` of this split imports it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/MatrixGeometry/TraceHomotopy.lean (declaration OAI.BorsukNine.Admissible.traceHomotopy_ray)

import Mathlib
import Definitions.Def_OAIQ058B000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator
open SimplicialChains
section TraceHomotopy
variable {ν ι : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι]
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι

omit [Nonempty ν] in
lemma Admissible.traceHomotopy_ray {f : EuclideanSpace ℝ ν → ι → ℝ} (_hf : Admissible f)
    (hc : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    (G : ℝ × traceSphere ν → Y)
    (hG : ContinuousOn G (Set.Icc (0:ℝ) 1 ×ˢ Set.univ))
    (hG0 : ∀ A : traceSphere ν, G (0,A) = WithLp.toLp 2 (signedExtension f A.val))
    (hGz : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ A : traceSphere ν, G (t,A) ≠ 0)
    {y : Y} (hy : y ≠ 0) :
    ∃ A : traceSphere ν, ∃ t : ℝ, 0 < t ∧ G (1,A) = t • y := by
  sorry

end TraceHomotopy
end BorsukNine

end OAI
end
