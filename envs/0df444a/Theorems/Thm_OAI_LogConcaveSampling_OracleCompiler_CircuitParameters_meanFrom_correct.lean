-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_OracleCompiler_CircuitParameters_meanFrom_correct
-- name    : OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom_correct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:27:33.836717+00:00
-- url     : https://prove2.me/theorems/e74fbe6e-197a-4565-b823-93c9e41cc758
-- title:
--   OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom_correct: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom_correct` of [lean/OAI/Probability/LogConcave/OraclePrograms/FullTape.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/OraclePrograms/FullTape.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters`, with `open MeanTree Coupling MeasureTheory ProbabilityTheory`, `open scoped Classical NNReal`):
--
--   ```lean
--   theorem meanFrom_correct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
--       {q Kf Ki Ks ef ei es en ηmin : ℝ} (hd : 1≤d) (hlam : (lam:ℝ)≤1)
--       (hq : 0≤q) (hql : q≤1/4) (hRT : Real.sqrt (1-C.T^2)≤C.T)
--       (hη : ηmin≤Real.sqrt (1-C.T^2)/C.T)
--       (hD : 1≤C.D) (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
--       (hKf : 0≤Kf) (hKi : 0≤Ki) (hKs : 0≤Ks)
--       (hef : 0<ef) (hei : 0≤ei) (hes : 0≤es) (hen : 0≤en)
--       (hsmall : 2*C.A*q*(2*Real.pi+2)≤1) (hcon : 4*C.A*q*Ki≤1) (hqs : q*Ks≤1)
--       (hm : C.m=C.n) (hnc : C.nc=C.n) (hNc : C.Nc=C.N)
--       (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
--       (B : ℕ) (hBD : (B:ℝ)≤C.D^2)
--       (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
--       (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
--       (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
--       (hS : SampleCorrect F lam (q/Real.sqrt (1-C.T^2)) Ks es ηmin S)
--       (hrsv : ∀r,(S r (Real.sqrt (1-C.T^2)/C.T)).reserve=(Real.sqrt (1-C.T^2)/C.T)/2)
--       (hnum : C.MeanNumericalReady hF q en hql) :
--       MeanCorrect F lam q (2*C.Af*C.depthBound*Kf)
--         (C.meanError C.depthBound Kf q es ei ef en) (C.meanFrom Mf Mi S)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters`, `OAI.LogConcaveSampling.OracleCompiler.MeanBudget`, `OAI.LogConcaveSampling.OracleCompiler.MeanCorrect`, `OAI.LogConcaveSampling.OracleCompiler.ReservedProgram`, `OAI.LogConcaveSampling.OracleCompiler.SampleCorrect`, `OAI.LogConcaveSampling.OracleCompiler.SeedProgram`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.MeanNumericalReady`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.actualA`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.actualAf`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.depthBound`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanError` and `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom` (definitions bundle `OAIQ048L002` of this split); `OAI.LogConcaveSampling.Point` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/OraclePrograms/FullTape.lean (declaration OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom_correct)

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
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree Coupling MeasureTheory ProbabilityTheory
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

theorem meanFrom_correct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki Ks ef ei es en ηmin : ℝ} (hd : 1≤d) (hlam : (lam:ℝ)≤1)
    (hq : 0≤q) (hql : q≤1/4) (hRT : Real.sqrt (1-C.T^2)≤C.T)
    (hη : ηmin≤Real.sqrt (1-C.T^2)/C.T)
    (hD : 1≤C.D) (hψ : 0≤C.ψ) (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0≤Kf) (hKi : 0≤Ki) (hKs : 0≤Ks)
    (hef : 0<ef) (hei : 0≤ei) (hes : 0≤es) (hen : 0≤en)
    (hsmall : 2*C.A*q*(2*Real.pi+2)≤1) (hcon : 4*C.A*q*Ki≤1) (hqs : q*Ks≤1)
    (hm : C.m=C.n) (hnc : C.nc=C.n) (hNc : C.Nc=C.N)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (B : ℕ) (hBD : (B:ℝ)≤C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (hS : SampleCorrect F lam (q/Real.sqrt (1-C.T^2)) Ks es ηmin S)
    (hrsv : ∀r,(S r (Real.sqrt (1-C.T^2)/C.T)).reserve=(Real.sqrt (1-C.T^2)/C.T)/2)
    (hnum : C.MeanNumericalReady hF q en hql) :
    MeanCorrect F lam q (2*C.Af*C.depthBound*Kf)
      (C.meanError C.depthBound Kf q es ei ef en) (C.meanFrom Mf Mi S) := by
  sorry
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
end
