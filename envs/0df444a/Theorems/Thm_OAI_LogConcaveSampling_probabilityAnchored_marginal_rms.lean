-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_probabilityAnchored_marginal_rms
-- name    : OAI.LogConcaveSampling.probabilityAnchored_marginal_rms
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:29:55.439989+00:00
-- url     : https://prove2.me/theorems/dfec953a-da42-4810-b1a2-fba5f607e6e6
-- title:
--   OAI.LogConcaveSampling.probabilityAnchored_marginal_rms: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.probabilityAnchored_marginal_rms` of [lean/OAI/Probability/LogConcave/Numerics/NodesContinuous.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Numerics/NodesContinuous.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling`, with `open Set MeasureTheory ProbabilityTheory FinitePicard`, `open scoped Classical BigOperators NNReal`):
--
--   ```lean
--   theorem probabilityAnchored_marginal_rms (n : ℕ) (hn : 0<n) :
--       ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
--         ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
--         0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
--         ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
--         A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀s i : ProbabilityNode T h n,
--         let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
--         let I : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n i,probabilityNodeTime_mem hT0 hT1 hh hn i⟩
--         Integrable (fun y => ‖probabilityAnchoredPicard F x r T h n N s y i-
--           probabilityTransport hF x hr.le hl hT0.le hT1 S I y‖^2)
--             (interpolationLaw F x r S) ∧
--         (∫y,‖probabilityAnchoredPicard F x r T h n N s y i-
--           probabilityTransport hF x hr.le hl hT0.le hT1 S I y‖^2
--             ∂interpolationLaw F x r S)≤
--           (4*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)+
--             (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*probabilityInitialRms F x lam r))^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive`, `OAI.LogConcaveSampling.ProbabilityNode`, `OAI.LogConcaveSampling.probabilityAnchoredPicard` and `OAI.LogConcaveSampling.probabilityNodeTime` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.probabilityMeanLipschitz` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.probabilityNodeTime_mem` (definitions bundle `OAIQ048L002` of this split); `OAI.LogConcaveSampling.interpolationLaw`, `OAI.LogConcaveSampling.probabilityInitialRms` and `OAI.LogConcaveSampling.probabilityTransport` (definitions bundle `OAIQ048L003` of this split); `OAI.LogConcaveSampling.Point` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.kernelCorrectionPicard_rms` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Numerics/NodesContinuous.lean (declaration OAI.LogConcaveSampling.probabilityAnchored_marginal_rms)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_OAIQ048L002
import Definitions.Def_OAIQ048L003

section

attribute [-instance] _root_.OAI.LogConcaveSampling.LowerBound.couplingLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.remainingHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.roundRandomLaw_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_invInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_isHaar _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_probability _root_.OAI.LogConcaveSampling.LowerBound.subspaceHaar_rightInvariant _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_compactSpace _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableInv _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_measurableMul _root_.OAI.LogConcaveSampling.LowerBound.subspaceStabilizer_secondCountable _root_.OAI.LogConcaveSampling.MeanTree.instIsProbabilityMeasureRowTapeRowLaw _root_.OAI.LogConcaveSampling.OracleCompiler.topSeedLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory FinitePicard
open scoped Classical BigOperators NNReal

theorem probabilityAnchored_marginal_rms (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0 < r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀s i : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let I : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n i,probabilityNodeTime_mem hT0 hT1 hh hn i⟩
      Integrable (fun y => ‖probabilityAnchoredPicard F x r T h n N s y i-
        probabilityTransport hF x hr.le hl hT0.le hT1 S I y‖^2)
          (interpolationLaw F x r S) ∧
      (∫y,‖probabilityAnchoredPicard F x r T h n N s y i-
        probabilityTransport hF x hr.le hl hT0.le hT1 S I y‖^2
          ∂interpolationLaw F x r S)≤
        (4*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)+
          (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*probabilityInitialRms F x lam r))^2 := by
  sorry

end LogConcaveSampling

end

end

end

end OAI
end
