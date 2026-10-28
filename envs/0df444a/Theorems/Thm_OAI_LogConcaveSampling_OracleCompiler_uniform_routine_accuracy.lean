-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_OracleCompiler_uniform_routine_accuracy
-- name    : OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:30:33.357108+00:00
-- url     : https://prove2.me/theorems/38f356f0-299d-46ac-b839-09621c386abe
-- title:
--   OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy` of [lean/OAI/Probability/LogConcave/OraclePrograms/StandaloneCorrect.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/OraclePrograms/StandaloneCorrect.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling.OracleCompiler`, with `open Filter MeanTree MeasureTheory ProbabilityTheory`, `open scoped Classical NNReal Topology`):
--
--   ```lean
--   theorem uniform_routine_accuracy {κ t w J K₀ : ℝ} {n N : ℕ}
--       (hκ : 0 < κ) (ht : 0 < t) (hts : t<1/100) (hw : 0 < w) (hwt : w<t)
--       (hJK : K₀≤J) (_ : N=numericalLayerCount J)
--       (hbudget : ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
--         ∃B : ℕ,(B:ℝ)≤C.D ∧ ∀L : RoutineLabel,L.Admissible t K₀ →
--         RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) 1 (constructRoutine d C ht (by linarith) L))
--       (hnum : ∀q : ℕ → ℝ,LogPowerRate q (κ*(1/2)) →
--         ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
--         ∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,0 < lam → (lam:ℝ)≤1 →
--         ∀hql : q d≤1/4,C.MeanNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) hql ∧
--         C.SampleNumericalReady hF (q d) ((d:ℝ)^(-(κ*J)))) :
--       ∀L : RoutineLabel,L.Admissible t K₀ → UniformAccuracy κ t w J n N ht (by linarith) L
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.LogPowerRate`, `OAI.LogConcaveSampling.numericalLayerCount`, `OAI.LogConcaveSampling.OracleCompiler.RoutineLabel` and `OAI.LogConcaveSampling.OracleCompiler.RoutineLabel.Admissible` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters`, `OAI.LogConcaveSampling.OracleCompiler.RoutineBudget`, `OAI.LogConcaveSampling.OracleCompiler.SourceShape`, `OAI.LogConcaveSampling.OracleCompiler.UniformAccuracy`, `OAI.LogConcaveSampling.OracleCompiler.constructRoutine`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.MeanNumericalReady` and `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.SampleNumericalReady` (definitions bundle `OAIQ048L002` of this split); `OAI.LogConcaveSampling.Point` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.eventually_subpolynomial_sampler` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/OraclePrograms/StandaloneCorrect.lean (declaration OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L002

section

attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler
open Filter MeanTree MeasureTheory ProbabilityTheory
open scoped Classical NNReal Topology

variable {d : ℕ}

theorem uniform_routine_accuracy {κ t w J K₀ : ℝ} {n N : ℕ}
    (hκ : 0 < κ) (ht : 0 < t) (hts : t<1/100) (hw : 0 < w) (hwt : w<t)
    (hJK : K₀≤J) (_ : N=numericalLayerCount J)
    (hbudget : ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∃B : ℕ,(B:ℝ)≤C.D ∧ ∀L : RoutineLabel,L.Admissible t K₀ →
      RoutineBudget B (Real.sqrt (1-C.T^2)/C.T) 1 (constructRoutine d C ht (by linarith) L))
    (hnum : ∀q : ℕ → ℝ,LogPowerRate q (κ*(1/2)) →
      ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,SourceShape κ t w n N d C →
      ∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,0 < lam → (lam:ℝ)≤1 →
      ∀hql : q d≤1/4,C.MeanNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) hql ∧
      C.SampleNumericalReady hF (q d) ((d:ℝ)^(-(κ*J)))) :
    ∀L : RoutineLabel,L.Admissible t K₀ → UniformAccuracy κ t w J n N ht (by linarith) L := by
  sorry
end LogConcaveSampling.OracleCompiler

end

end

end OAI
end
