-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_OracleCompiler_CircuitParameters_sampleFrom_squared
-- name    : OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleFrom_squared
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:29:27.847933+00:00
-- url     : https://prove2.me/theorems/c8a71d68-b974-4105-bc97-8695c8999505
-- title:
--   OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleFrom_squared: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleFrom_squared` of [lean/OAI/Probability/LogConcave/OraclePrograms/FullTape.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/OraclePrograms/FullTape.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters`, with `open MeasureTheory ProbabilityTheory MeanTree Coupling Function`, `open scoped Classical NNReal`):
--
--   ```lean
--   theorem sampleFrom_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
--       {q Kf Ki ef ei r η en : ℝ} (hd : 1 ≤ d)
--       (hs : SampleSize lam q r η) (hl : q ≤ 1/4) (hL : (lam:ℝ)*r ≤ 1)
--       (hRη : Real.sqrt (1-C.T^2) ≤ η) (hD : 1 ≤ C.D)
--       (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
--       (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 < ef) (hei : 0 ≤ ei)
--       (hsmall : (lam:ℝ)*C.sampleCenterBudget r*(2*Real.pi+2) ≤ 1)
--       (hcon : 4*(C.sampleCenterBudget r)^2*((lam:ℝ)*Ki)^2 ≤ 1)
--       (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
--       (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
--       (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
--       (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
--       (x : Point d)
--       (hlr : (lam:ℝ)*r^2 ≤ 1/2)
--       (hnumi : Integrable (fun Y => ‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
--         (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
--         (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hlr (sampleCorrelation η) Y‖^2)
--         (stdGaussian (Point d)))
--       (hnum : (∫Y,‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
--         (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
--         (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hlr (sampleCorrelation η) Y‖^2
--         ∂stdGaussian (Point d)) ≤ (circuitD F x)^2*en^2) :
--       let dep := (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)
--       let a := 2*(1+dep)*(C.Af*Kf*q*ei+ef)
--       SquaredAt (gaussianTape d (C.sampleFrom Mf Mi r η).slots)
--         ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
--         (fun g => (C.sampleFrom Mf Mi r η).pre.run F (x,g))
--         (fun z => z.1+(Real.sqrt 3*η/2) • z.2)
--         ((400*(η*a)^2+4*en^2)*(circuitD F x)^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive`, `OAI.LogConcaveSampling.circuitD`, `OAI.LogConcaveSampling.primitivePotential`, `OAI.LogConcaveSampling.Coupling.SquaredAt`, `OAI.LogConcaveSampling.MeanTree.depth` and `OAI.LogConcaveSampling.OracleCompiler.Program.run` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.sampleCorrelation` and `OAI.LogConcaveSampling.OracleCompiler.SampleSize` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.fullProbabilityFlow`, `OAI.LogConcaveSampling.gaussianTape`, `OAI.LogConcaveSampling.sampleMeanCircuit`, `OAI.LogConcaveSampling.MeanTree.SampleInput`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters`, `OAI.LogConcaveSampling.OracleCompiler.MeanBudget`, `OAI.LogConcaveSampling.OracleCompiler.MeanCorrect`, `OAI.LogConcaveSampling.OracleCompiler.SeedProgram`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.actualA`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.actualAf`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleCenterBudget`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleEndpoint`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleFrom`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleTree` and `OAI.LogConcaveSampling.OracleCompiler.ReservedProgram` (definitions bundle `OAIQ048L002` of this split); `OAI.LogConcaveSampling.Point` and `OAI.LogConcaveSampling.gibbs` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.OracleCompiler.uniform_routine_accuracy` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/OraclePrograms/FullTape.lean (declaration OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.sampleFrom_squared)

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
open MeasureTheory ProbabilityTheory MeanTree Coupling Function
open scoped Classical NNReal

variable (C : CircuitParameters) {d : ℕ}

theorem sampleFrom_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {q Kf Ki ef ei r η en : ℝ} (hd : 1 ≤ d)
    (hs : SampleSize lam q r η) (hl : q ≤ 1/4) (hL : (lam:ℝ)*r ≤ 1)
    (hRη : Real.sqrt (1-C.T^2) ≤ η) (hD : 1 ≤ C.D)
    (hA : C.A=C.actualA) (hAf : C.Af=C.actualAf)
    (hKf : 0 ≤ Kf) (hKi : 0 ≤ Ki) (hef : 0 < ef) (hei : 0 ≤ ei)
    (hsmall : (lam:ℝ)*C.sampleCenterBudget r*(2*Real.pi+2) ≤ 1)
    (hcon : 4*(C.sampleCenterBudget r)^2*((lam:ℝ)*Ki)^2 ≤ 1)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (B : ℕ) (hBD : (B:ℝ) ≤ C.D^2)
    (hbudget : ∀(s : Bool) r τ,MeanBudget B r ((if s then Mf else Mi) r τ))
    (hf : MeanCorrect F lam ((1+4*C.Af)*q) Kf ef Mf)
    (hi : MeanCorrect F lam (q*(1+16*C.D*C.A/Real.sqrt (1-C.T^2))) Ki ei Mi)
    (x : Point d)
    (hlr : (lam:ℝ)*r^2 ≤ 1/2)
    (hnumi : Integrable (fun Y => ‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
      (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
      (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hlr (sampleCorrelation η) Y‖^2)
      (stdGaussian (Point d)))
    (hnum : (∫Y,‖sampleMeanCircuit F x r (sampleCorrelation η) C.h
      (C.n+1) C.N (C.sampleEndpoint η hs.2.2.1 hs.2.2.2.1) Y-
      (sampleCorrelation η)⁻¹ • fullProbabilityFlow hF x hs.1.le hlr (sampleCorrelation η) Y‖^2
      ∂stdGaussian (Point d)) ≤ (circuitD F x)^2*en^2) :
    let dep := (depth (C.sampleTree (d:=d) r η hs.2.2.1 hs.2.2.2.1):ℝ)
    let a := 2*(1+dep)*(C.Af*Kf*q*ei+ef)
    SquaredAt (gaussianTape d (C.sampleFrom Mf Mi r η).slots)
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => (C.sampleFrom Mf Mi r η).pre.run F (x,g))
      (fun z => z.1+(Real.sqrt 3*η/2) • z.2)
      ((400*(η*a)^2+4*en^2)*(circuitD F x)^2) := by
  sorry
end LogConcaveSampling.OracleCompiler.CircuitParameters

end

end

end OAI
end
