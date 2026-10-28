-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_exists_centering_stationaryPath
-- name    : OAI.LogConcaveSampling.exists_centering_stationaryPath
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:23:32.64886+00:00
-- url     : https://prove2.me/theorems/86f39be4-d93a-40b6-a3dd-71c05f61a0b5
-- title:
--   OAI.LogConcaveSampling.exists_centering_stationaryPath: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.exists_centering_stationaryPath` of [lean/OAI/Probability/LogConcave/Dynamics/StationaryPath.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Dynamics/StationaryPath.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling`, with `open Set MeasureTheory Quadrature TensorEnergy`, `open scoped Classical BigOperators NNReal`):
--
--   ```lean
--   theorem exists_centering_stationaryPath {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
--       (hF : Primitive F lam) (x : Point d) {r T s : ℝ} (hr : 0 < r) (hlam : 0<lam)
--       (hl : (lam:ℝ)*r^2 ≤ 1/2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s) :
--       Nonempty (StationaryPath (gibbs (centeringPotential F x r T))
--         (skewLieField (centeringPotential F x r T)
--           (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive`, `OAI.LogConcaveSampling.StationaryPath`, `OAI.LogConcaveSampling.centeringKernel`, `OAI.LogConcaveSampling.centeringPotential`, `OAI.LogConcaveSampling.jointSkew` and `OAI.LogConcaveSampling.skewLieField` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.Point` and `OAI.LogConcaveSampling.gibbs` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Dynamics/StationaryPath.lean (declaration OAI.LogConcaveSampling.exists_centering_stationaryPath)

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
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

theorem exists_centering_stationaryPath {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T s : ℝ} (hr : 0 < r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s) :
    Nonempty (StationaryPath (gibbs (centeringPotential F x r T))
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s))) := by
  sorry

end LogConcaveSampling

end

end

end OAI
end
