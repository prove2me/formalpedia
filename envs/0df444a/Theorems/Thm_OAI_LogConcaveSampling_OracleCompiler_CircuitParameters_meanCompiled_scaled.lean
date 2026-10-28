-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_OracleCompiler_CircuitParameters_meanCompiled_scaled
-- name    : OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanCompiled_scaled
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:32:08.286289+00:00
-- url     : https://prove2.me/theorems/6c11e447-4787-45f7-b08f-5e49e15580d1
-- title:
--   OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanCompiled_scaled (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanCompiled_scaled` of [lean/OAI/Probability/LogConcave/OraclePrograms/ShiftInvariant.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/OraclePrograms/ShiftInvariant.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters`, with `open MeanTree MeasureTheory ProbabilityTheory Coupling SeedCompiler`, `open scoped Classical NNReal`):
--
--   ```lean
--   lemma meanCompiled_scaled {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
--       {q Kf Ki ef ei r σ : ℝ} (hs : MeanSize lam q r σ) (hl : q ≤ 1/2)
--       (hL : (lam:ℝ)*r ≤ 1) (hD : 1 ≤ C.D) (hψ : 0 ≤ C.ψ)
--       (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
--       (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 ≤ ef) (hei : 0 ≤ ei)
--       (hsmall : (lam:ℝ)*C.meanCenterBudget r σ*(2*Real.pi+2) ≤ 1)
--       (hcon : 4*(C.meanCenterBudget r σ)^2*((lam:ℝ)*Ki)^2 ≤ 1)
--       (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
--       (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
--       (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
--       (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
--       (x Y G : Point d) :
--       let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi
--         (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2)
--       let a := 2*(1+2*(depth (C.meanTree (d:=d) r σ):ℝ))*(C.Af*Kf*q*ei+ef)
--       SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d)) (E.eval F (x,(Y,G)))
--         (fun g => (C.meanTree r σ).eval F (x,(Y,G))+(Real.sqrt 3*σ/2) • g)
--         ((σ*a)^2*(pairGauge (circuitD F x) (Y,G))^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive`, `OAI.LogConcaveSampling.circuitD`, `OAI.LogConcaveSampling.Coupling.SquaredAt`, `OAI.LogConcaveSampling.MeanTree.depth` and `OAI.LogConcaveSampling.MeanTree.eval` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.OracleCompiler.MeanSize` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.gaussianTape`, `OAI.LogConcaveSampling.MeanTree.MeanInput`, `OAI.LogConcaveSampling.MeanTree.compileDeclaredRoot`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters`, `OAI.LogConcaveSampling.OracleCompiler.Expression`, `OAI.LogConcaveSampling.OracleCompiler.MeanBudget`, `OAI.LogConcaveSampling.OracleCompiler.MeanCorrect`, `OAI.LogConcaveSampling.OracleCompiler.SeedProgram`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.actualA`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.actualAf`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanCenterBudget`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanTree`, `OAI.LogConcaveSampling.OracleCompiler.Expression.eval` and `OAI.LogConcaveSampling.OracleCompiler.Expression.slots` (definitions bundle `OAIQ048L002` of this split); `OAI.LogConcaveSampling.pairGauge` (definitions bundle `OAIQ048L004` of this split); `OAI.LogConcaveSampling.Point` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanFrom_correct` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/OraclePrograms/ShiftInvariant.lean (declaration OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.meanCompiled_scaled)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L004

section

attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability _root_.OAI.LogConcaveSampling.noiseKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace LogConcaveSampling.OracleCompiler.CircuitParameters
open MeanTree MeasureTheory ProbabilityTheory Coupling SeedCompiler
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

lemma meanCompiled_scaled {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r σ : ℝ} (hs : MeanSize lam q r σ) (hl : q ≤ 1/2)
    (hL : (lam:ℝ)*r ≤ 1) (hD : 1 ≤ C.D) (hψ : 0 ≤ C.ψ)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 ≤ ef) (hei : 0 ≤ ei)
    (hsmall : (lam:ℝ)*C.meanCenterBudget r σ*(2*Real.pi+2) ≤ 1)
    (hcon : 4*(C.meanCenterBudget r σ)^2*((lam:ℝ)*Ki)^2 ≤ 1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*Real.sqrt (1-C.T^2)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x Y G : Point d) :
    let E := compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi
      (C.meanTree (d:=d) r σ) (Real.sqrt 3*σ/2)
    let a := 2*(1+2*(depth (C.meanTree (d:=d) r σ):ℝ))*(C.Af*Kf*q*ei+ef)
    SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d)) (E.eval F (x,(Y,G)))
      (fun g => (C.meanTree r σ).eval F (x,(Y,G))+(Real.sqrt 3*σ/2) • g)
      ((σ*a)^2*(pairGauge (circuitD F x) (Y,G))^2) := by
  sorry

end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
end
