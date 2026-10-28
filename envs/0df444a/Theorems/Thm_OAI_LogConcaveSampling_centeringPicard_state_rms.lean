-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_centeringPicard_state_rms
-- name    : OAI.LogConcaveSampling.centeringPicard_state_rms
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:36:33.008361+00:00
-- url     : https://prove2.me/theorems/667b7460-6238-4aca-9878-36d59a6bd091
-- title:
--   OAI.LogConcaveSampling.centeringPicard_state_rms: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.centeringPicard_state_rms` of [lean/OAI/Probability/LogConcave/OraclePrograms/CenteringMeanCircuit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/OraclePrograms/CenteringMeanCircuit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling`, with `open Set MeasureTheory Quadrature`, `open scoped Classical BigOperators NNReal`):
--
--   ```lean
--   theorem centeringPicard_state_rms (n m N nc Nc : ℕ) (hnc : 0<nc)
--       (e : ProbabilityNode T h (n+1)) {K : ℝ≥0}
--       (hhat : LipschitzWith K (centeringVelocityJoint F x r T h ψ s n m N e))
--       (hq : centeringRowBudget nc*K ≤ 1/2) {Bv : ℝ} (hBv : 0 ≤ Bv)
--       (hvi : Integrable (fun y => ‖centeringVelocityJoint F x r T h ψ s n m N e y-
--         skewLieField (centeringPotential F x r T)
--           (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y‖^2)
--         (gibbs (centeringPotential F x r T)))
--       (hvb : (∫y,‖centeringVelocityJoint F x r T h ψ s n m N e y-
--         skewLieField (centeringPotential F x r T)
--           (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y‖^2
--         ∂gibbs (centeringPotential F x r T)) ≤ Bv) (i : Fin (nc+1)) :
--       Integrable (fun y => ‖stationaryPicard nc Nc
--         (centeringVelocityJoint F x r T h ψ s n m N e) y i-X.path y (probabilityNodes nc i)‖^2)
--         (gibbs (centeringPotential F x r T)) ∧
--       (∫y,‖stationaryPicard nc Nc (centeringVelocityJoint F x r T h ψ s n m N e) y i-
--         X.path y (probabilityNodes nc i)‖^2 ∂gibbs (centeringPotential F x r T)) ≤
--         centeringPicardBudget nc Nc d lam K r R s Bv
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive`, `OAI.LogConcaveSampling.ProbabilityNode`, `OAI.LogConcaveSampling.StationaryPath`, `OAI.LogConcaveSampling.centeringKernel`, `OAI.LogConcaveSampling.centeringPotential`, `OAI.LogConcaveSampling.centeringVelocityJoint`, `OAI.LogConcaveSampling.jointSkew`, `OAI.LogConcaveSampling.probabilityNodes`, `OAI.LogConcaveSampling.skewLieField` and `OAI.LogConcaveSampling.stationaryPicard` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.centeringPicardBudget` and `OAI.LogConcaveSampling.centeringRowBudget` (definitions bundle `OAIQ048L004` of this split); `OAI.LogConcaveSampling.Point` and `OAI.LogConcaveSampling.gibbs` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/OraclePrograms/CenteringMeanCircuit.lean (declaration OAI.LogConcaveSampling.centeringPicard_state_rms)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004

section

attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r R T h ψ s : ℝ}
  (hr : 0 < r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
  (hR : 0<R) (hRT : R^2 ≤ 1-T^2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0 < s)
  (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T) (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))

include hlam hR hRT hs

theorem centeringPicard_state_rms (n m N nc Nc : ℕ) (hnc : 0<nc)
    (e : ProbabilityNode T h (n+1)) {K : ℝ≥0}
    (hhat : LipschitzWith K (centeringVelocityJoint F x r T h ψ s n m N e))
    (hq : centeringRowBudget nc*K ≤ 1/2) {Bv : ℝ} (hBv : 0 ≤ Bv)
    (hvi : Integrable (fun y => ‖centeringVelocityJoint F x r T h ψ s n m N e y-
      skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y‖^2)
      (gibbs (centeringPotential F x r T)))
    (hvb : (∫y,‖centeringVelocityJoint F x r T h ψ s n m N e y-
      skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y‖^2
      ∂gibbs (centeringPotential F x r T)) ≤ Bv) (i : Fin (nc+1)) :
    Integrable (fun y => ‖stationaryPicard nc Nc
      (centeringVelocityJoint F x r T h ψ s n m N e) y i-X.path y (probabilityNodes nc i)‖^2)
      (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖stationaryPicard nc Nc (centeringVelocityJoint F x r T h ψ s n m N e) y i-
      X.path y (probabilityNodes nc i)‖^2 ∂gibbs (centeringPotential F x r T)) ≤
      centeringPicardBudget nc Nc d lam K r R s Bv := by
  sorry

end LogConcaveSampling

end

end

end OAI
end
