-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_stationaryMeanTarget_law
-- name    : OAI.LogConcaveSampling.stationaryMeanTarget_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:25:26.01741+00:00
-- url     : https://prove2.me/theorems/a4e65de8-0468-4633-bc3a-1f13c705f410
-- title:
--   OAI.LogConcaveSampling.stationaryMeanTarget_law: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.stationaryMeanTarget_law` of [lean/OAI/Probability/LogConcave/Sampling/StationaryMeanTarget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Sampling/StationaryMeanTarget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling`, with `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators NNReal`):
--
--   ```lean
--   theorem stationaryMeanTarget_law :
--       (gibbs (centeringPotential F x r T)).map (stationaryMeanTarget hF x hr hl hT0 hT1 X)=
--         (stdGaussian (Point d)).map (fun g => primitiveExpectedField F x r+s • g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive`, `OAI.LogConcaveSampling.StationaryPath`, `OAI.LogConcaveSampling.centeringKernel`, `OAI.LogConcaveSampling.centeringPotential`, `OAI.LogConcaveSampling.jointSkew`, `OAI.LogConcaveSampling.primitiveExpectedField`, `OAI.LogConcaveSampling.skewLieField` and `OAI.LogConcaveSampling.stationaryMeanTarget` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.Point` and `OAI.LogConcaveSampling.gibbs` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Sampling/StationaryMeanTarget.lean (declaration OAI.LogConcaveSampling.stationaryMeanTarget_law)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T s : ℝ}
  (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
  (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s)
  (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))

include hlam hs in

theorem stationaryMeanTarget_law :
    (gibbs (centeringPotential F x r T)).map (stationaryMeanTarget hF x hr hl hT0 hT1 X)=
      (stdGaussian (Point d)).map (fun g => primitiveExpectedField F x r+s • g) := by
  sorry
end LogConcaveSampling

end

end

end OAI
end
