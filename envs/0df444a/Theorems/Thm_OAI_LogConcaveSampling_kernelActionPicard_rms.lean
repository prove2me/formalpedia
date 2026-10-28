-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_kernelActionPicard_rms
-- name    : OAI.LogConcaveSampling.kernelActionPicard_rms
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:36:26.562846+00:00
-- url     : https://prove2.me/theorems/ded28281-53ce-437c-a413-c405fab11e01
-- title:
--   OAI.LogConcaveSampling.kernelActionPicard_rms: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.kernelActionPicard_rms` of [lean/OAI/Probability/LogConcave/Numerics/KernelActionPicardRms.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Numerics/KernelActionPicardRms.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling`, with `open Set MeasureTheory ProbabilityTheory Quadrature`, `open scoped Classical BigOperators NNReal`):
--
--   ```lean
--   theorem kernelActionPicard_rms (n : ℕ) (hn : 0<n) :
--       ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
--         ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
--         ∀(x : Point d) {r : ℝ},∀hr : 0 < r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
--         ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
--         Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
--         Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
--         ∀N : ℕ,∀s e : ProbabilityNode T h n,
--         let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
--         let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
--         let μ := gibbs (centeringPotential F x r S)
--         let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
--         ∀R : ℝ,0<R → R^2≤1-T^2 →
--         ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
--         let err := fun y => kernelActionPicard F x r T h ψ n m N s e
--           (fw (productPointEquiv d d y).1,(productPointEquiv d d y).2)-kernelTransportAction fw y
--         Integrable (fun y => ‖err y‖^2) μ ∧
--         (∫y,‖err y‖^2 ∂μ)≤
--           2*((∑i,|derivativeWeight (angleNodes m) i/ψ|)*
--             (∑i,|derivativeWeight (angleNodes m) i/ψ| *
--               kernelValueRmsBudget F x lam Ap Ah Lp r R S h (ψ*angleNodes m i) C J k n N))+
--           2*(((∑i,|derivativeWeight (angleNodes m) i|)/ψ)^2*
--             (((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
--               ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive`, `OAI.LogConcaveSampling.ProbabilityNode`, `OAI.LogConcaveSampling.angleNodes`, `OAI.LogConcaveSampling.centeringPotential`, `OAI.LogConcaveSampling.kernelActionPicard`, `OAI.LogConcaveSampling.probabilityNodeTime`, `OAI.LogConcaveSampling.productPointEquiv` and `OAI.LogConcaveSampling.Quadrature.derivativeWeight` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.probabilityMeanLipschitz` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.probabilityNodeTime_mem` (definitions bundle `OAIQ048L002` of this split); `OAI.LogConcaveSampling.kernelTransportAction`, `OAI.LogConcaveSampling.kernelValueRmsBudget` and `OAI.LogConcaveSampling.probabilityTransport` (definitions bundle `OAIQ048L003` of this split); `OAI.LogConcaveSampling.harmonicCorrectionBudget` (definitions bundle `OAIQ048L004` of this split); `OAI.LogConcaveSampling.Point` and `OAI.LogConcaveSampling.gibbs` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.kernelQuadraturePicard_full_rms` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Numerics/KernelActionPicardRms.lean (declaration OAI.LogConcaveSampling.kernelActionPicard_rms)

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
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

theorem kernelActionPicard_rms (n : ℕ) (hn : 0<n) :
    ∃Ap Ah Lp Lh : ℝ≥0,∃C J : ℝ,0≤C ∧ 1≤J ∧ ∃k : ℕ,
      ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,
      ∀(x : Point d) {r : ℝ},∀hr : 0 < r,0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      Ap*probabilityMeanLipschitz lam r≤1/2 → Ah*probabilityMeanLipschitz lam r≤1/2 →
      Lp*probabilityMeanLipschitz lam r≤1/2 → Lh*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀s e : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
      let μ := gibbs (centeringPotential F x r S)
      let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
      ∀R : ℝ,0<R → R^2≤1-T^2 →
      ∀m : ℕ,1 ≤ m → ∀ψ : ℝ,0<ψ → ψ*m≤1 →
      let err := fun y => kernelActionPicard F x r T h ψ n m N s e
        (fw (productPointEquiv d d y).1,(productPointEquiv d d y).2)-kernelTransportAction fw y
      Integrable (fun y => ‖err y‖^2) μ ∧
      (∫y,‖err y‖^2 ∂μ)≤
        2*((∑i,|derivativeWeight (angleNodes m) i/ψ|)*
          (∑i,|derivativeWeight (angleNodes m) i/ψ| *
            kernelValueRmsBudget F x lam Ap Ah Lp r R S h (ψ*angleNodes m i) C J k n N))+
        2*(((∑i,|derivativeWeight (angleNodes m) i|)/ψ)^2*
          (((ψ*m)^(m+1)/(m.factorial:ℝ))^2*
            ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(m+1))*harmonicCorrectionBudget (m+1)))) := by
  sorry
end LogConcaveSampling

end

end

end

end OAI
end
