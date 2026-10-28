-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_kernelQuadraturePicard_full_rms
-- name    : OAI.LogConcaveSampling.kernelQuadraturePicard_full_rms
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:37:51.155012+00:00
-- url     : https://prove2.me/theorems/cd2ecf7f-1e59-4de1-a60b-f0790c1c1dfc
-- title:
--   OAI.LogConcaveSampling.kernelQuadraturePicard_full_rms: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.kernelQuadraturePicard_full_rms` of [lean/OAI/Probability/LogConcave/Numerics/CenteringVelocityPicard.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Numerics/CenteringVelocityPicard.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling`, with `open Set MeasureTheory ProbabilityTheory Quadrature`, `open scoped Classical BigOperators NNReal`):
--
--   ```lean
--   theorem kernelQuadraturePicard_full_rms (n : ℕ) :
--       ∃Ap Ah Lp Lh : ℝ≥0,∃C J D : ℝ,0≤C ∧ 1≤J ∧ 1≤D ∧ ∃k : ℕ,
--         ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
--         ∀(x : Point d) {r : ℝ},∀hr : 0 < r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
--         ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 → h≤logMeshLength T →
--         Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
--         Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
--         ∀N : ℕ,∀R : ℝ,0<R → R^2≤1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
--         let w := terminalQuadratureWeight T h n
--         let err := fun p : Point d × Point d =>
--           kernelQuadraturePicard F x r T h ψ (n+1) m N (probabilityEndpoint hT0 hT1 hh (n+1)) w p-
--             r • (centeringKernel hF x hr hl hT0.le hT1 p.1).adjoint p.2
--         Integrable (fun p => ‖err p‖^2) ((interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
--         (∫p,‖err p‖^2 ∂((interpolationLaw F x r T).prod (stdGaussian (Point d))))≤
--           2*((∑s,|w s|)*(∑s,|w s| *
--             kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h (n+1) s) h ψ C J k (n+1) m N))+
--           2*kernelAnalyticBudget n d lam r T h D
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive`, `OAI.LogConcaveSampling.ProbabilityNode`, `OAI.LogConcaveSampling.centeringKernel`, `OAI.LogConcaveSampling.kernelQuadraturePicard`, `OAI.LogConcaveSampling.probabilityEndpoint`, `OAI.LogConcaveSampling.probabilityNodeTime`, `OAI.LogConcaveSampling.terminalQuadratureWeight`, `OAI.LogConcaveSampling.Quadrature.logMeshCount` and `OAI.LogConcaveSampling.Quadrature.logMeshLength` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.probabilityMeanLipschitz` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.interpolationLaw` (definitions bundle `OAIQ048L003` of this split); `OAI.LogConcaveSampling.kernelActionRmsBudget` and `OAI.LogConcaveSampling.kernelAnalyticBudget` (definitions bundle `OAIQ048L004` of this split); `OAI.LogConcaveSampling.Point` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.centeringVelocityJoint_full_rms` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Numerics/CenteringVelocityPicard.lean (declaration OAI.LogConcaveSampling.kernelQuadraturePicard_full_rms)

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
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

theorem kernelQuadraturePicard_full_rms (n : ℕ) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J D : ℝ,0≤C ∧ 1≤J ∧ 1≤D ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0 < r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 → h≤logMeshLength T →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀R : ℝ,0<R → R^2≤1-T^2 → ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
      let w := terminalQuadratureWeight T h n
      let err := fun p : Point d × Point d =>
        kernelQuadraturePicard F x r T h ψ (n+1) m N (probabilityEndpoint hT0 hT1 hh (n+1)) w p-
          r • (centeringKernel hF x hr hl hT0.le hT1 p.1).adjoint p.2
      Integrable (fun p => ‖err p‖^2) ((interpolationLaw F x r T).prod (stdGaussian (Point d))) ∧
      (∫p,‖err p‖^2 ∂((interpolationLaw F x r T).prod (stdGaussian (Point d))))≤
        2*((∑s,|w s|)*(∑s,|w s| *
          kernelActionRmsBudget F x lam Ap Ah Lp r R (probabilityNodeTime T h (n+1) s) h ψ C J k (n+1) m N))+
        2*kernelAnalyticBudget n d lam r T h D := by
  sorry
end LogConcaveSampling

end

end

end OAI
end
