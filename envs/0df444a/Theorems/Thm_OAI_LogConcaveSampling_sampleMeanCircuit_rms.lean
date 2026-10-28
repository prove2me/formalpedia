-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_sampleMeanCircuit_rms
-- name    : OAI.LogConcaveSampling.sampleMeanCircuit_rms
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:33:29.366594+00:00
-- url     : https://prove2.me/theorems/f831bcfd-9351-4f4e-904c-073638a5b9c4
-- title:
--   OAI.LogConcaveSampling.sampleMeanCircuit_rms: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.sampleMeanCircuit_rms` of [lean/OAI/Probability/LogConcave/Numerics/Forward.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Numerics/Forward.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling`, with `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators NNReal`):
--
--   ```lean
--   theorem sampleMeanCircuit_rms (n : ℕ) (hn : 0<n) :
--       ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
--         ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
--         r≤1 → 0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,(lam:ℝ)*r≤1 → 1≤d →
--         ∀{T h : ℝ},1/2≤T → T<1 → 0<h → h≤Real.log 2 →
--         A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀e : ProbabilityNode T h n,
--         Integrable (fun z => ‖sampleMeanCircuit F x r T h n N e z-
--           T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2)
--           (stdGaussian (Point d)) ∧
--         (∫z,‖sampleMeanCircuit F x r T h n N e z-
--           T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2 ∂stdGaussian (Point d))≤
--           (circuitD F x)^2*samplingEnvelope d k n N C (A*probabilityMeanLipschitz lam r) h
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive`, `OAI.LogConcaveSampling.ProbabilityNode`, `OAI.LogConcaveSampling.circuitD` and `OAI.LogConcaveSampling.probabilityNodeTime` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.probabilityMeanLipschitz` and `OAI.LogConcaveSampling.samplingEnvelope` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.fullProbabilityFlow` and `OAI.LogConcaveSampling.sampleMeanCircuit` (definitions bundle `OAIQ048L002` of this split); `OAI.LogConcaveSampling.Point` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Numerics/Forward.lean (declaration OAI.LogConcaveSampling.sampleMeanCircuit_rms)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L002

section

attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
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

theorem sampleMeanCircuit_rms (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
      r≤1 → 0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,(lam:ℝ)*r≤1 → 1≤d →
      ∀{T h : ℝ},1/2≤T → T<1 → 0<h → h≤Real.log 2 →
      A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀e : ProbabilityNode T h n,
      Integrable (fun z => ‖sampleMeanCircuit F x r T h n N e z-
        T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖sampleMeanCircuit F x r T h n N e z-
        T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2 ∂stdGaussian (Point d))≤
        (circuitD F x)^2*samplingEnvelope d k n N C (A*probabilityMeanLipschitz lam r) h := by
  sorry
end LogConcaveSampling

end

end

end OAI
end
