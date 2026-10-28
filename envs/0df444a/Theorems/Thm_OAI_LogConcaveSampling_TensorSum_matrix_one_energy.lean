-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_TensorSum_matrix_one_energy
-- name    : OAI.LogConcaveSampling.TensorSum.matrix_one_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:35:13.191865+00:00
-- url     : https://prove2.me/theorems/33cf3dc2-0cd4-4d26-9e1e-dcbcf981b576
-- title:
--   OAI.LogConcaveSampling.TensorSum.matrix_one_energy: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.TensorSum.matrix_one_energy` of [lean/OAI/Probability/LogConcave/Sampling/MatrixColor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Sampling/MatrixColor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling.TensorSum`, with `open MeasureTheory`, `open scoped Classical BigOperators NNReal`):
--
--   ```lean
--   lemma matrix_one_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
--       (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
--       (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
--       (hd : 1≤d) (A : TensorSum (Unit ⊕ Unit)) {w : ℕ} (hw : A.weightLE w) :
--       (∑a : Fin d,∫y,∑i : Fin d,∑j : Fin d,(directional (EuclideanSpace.basisFun (Fin d) ℝ i)
--         (A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j))) y)^2
--          ∂interpolationLaw F x r ρ)≤d*(A.momentBudget d 1 2).toReal^2*((Real.sqrt (1-ρ^2))⁻¹)^(2*(w+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive` and `OAI.LogConcaveSampling.directional` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.TensorSum`, `OAI.LogConcaveSampling.TensorSum.momentBudget` and `OAI.LogConcaveSampling.TensorSum.weightLE` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.interpolationLaw` (definitions bundle `OAIQ048L003` of this split); `OAI.LogConcaveSampling.TensorSum.slice` (definitions bundle `OAIQ048L004` of this split); `OAI.LogConcaveSampling.Point` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proofs of `OAI.LogConcaveSampling.probabilityAnchored_marginal_rms` and `OAI.LogConcaveSampling.sampleMeanCircuit_rms` of this split import it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Sampling/MatrixColor.lean (declaration OAI.LogConcaveSampling.TensorSum.matrix_one_energy)

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
open MeasureTheory
open scoped Classical BigOperators NNReal

namespace TensorSum

lemma matrix_one_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorSum (Unit ⊕ Unit)) {w : ℕ} (hw : A.weightLE w) :
    (∑a : Fin d,∫y,∑i : Fin d,∑j : Fin d,(directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (A.slice F x r ρ ((lam:ℝ)*r) (Sum.elim (fun _ => a) (fun _ => j))) y)^2
       ∂interpolationLaw F x r ρ)≤d*(A.momentBudget d 1 2).toReal^2*((Real.sqrt (1-ρ^2))⁻¹)^(2*(w+1)) := by
  sorry
end TensorSum
end LogConcaveSampling

end

end

end

end OAI
end
