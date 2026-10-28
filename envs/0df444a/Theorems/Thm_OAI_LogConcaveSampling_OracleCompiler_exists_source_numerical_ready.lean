-- Prove2me | Theorems.Thm_OAI_LogConcaveSampling_OracleCompiler_exists_source_numerical_ready
-- name    : OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T13:30:19.954193+00:00
-- url     : https://prove2.me/theorems/e52973f1-c490-44a8-a9c6-fa3821052b20
-- title:
--   OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready: intermediate lemma from OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogConcaveSampling.exact_source_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139)*, OpenAI Math Release, September 26, 2026, result family 139, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready` of [lean/OAI/Probability/LogConcave/Complexity/Envelope.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Complexity/Envelope.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LogConcaveSampling.OracleCompiler`, with `open Filter MeasureTheory ProbabilityTheory`, `open scoped Classical NNReal Topology`):
--
--   ```lean
--   theorem exists_source_numerical_ready {κ J t w : ℝ}
--       (hκ : 0<κ) (hJ : 1≤J) (ht : 0<t) (hts : t<1/100)
--       (hw : 0<w) (hwt : w<t) : ∃n : ℕ,
--       J+10<w*((n:ℝ)-3) ∧ J+10<t*((n:ℝ)-3) ∧ 4*(J+10)<(n:ℝ) ∧
--       ∀q : ℕ → ℝ,LogPowerRate q (κ*(1/2)) →
--         ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,
--         SourceShape κ t w n (numericalLayerCount J) d C →
--         ∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,0<lam → (lam:ℝ)≤1 →
--         ∀hql : q d≤1/4,
--         C.MeanNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) hql ∧
--         C.SampleNumericalReady hF (q d) ((d:ℝ)^(-(κ*J)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.LogConcaveSampling.Primitive` (definitions bundle `OAIQ048L000` of this split); `OAI.LogConcaveSampling.LogPowerRate` and `OAI.LogConcaveSampling.numericalLayerCount` (definitions bundle `OAIQ048L001` of this split); `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters`, `OAI.LogConcaveSampling.OracleCompiler.SourceShape`, `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.MeanNumericalReady` and `OAI.LogConcaveSampling.OracleCompiler.CircuitParameters.SampleNumericalReady` (definitions bundle `OAIQ048L002` of this split); `OAI.LogConcaveSampling.Point` (the published bundle `Def_LogConcaveQuery`).
--
--   **Used by.** The proof of `OAI.LogConcaveSampling.eventually_subpolynomial_sampler` of this split imports it.
-- source:
--   OpenAI, Subpolynomial query complexity for well-conditioned log-concave sampling (result family 139), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 139; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Subpolynomial-query-complexity-for-well-conditioned-log-concave-sampling-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/LogConcave/Complexity/Envelope.lean (declaration OAI.LogConcaveSampling.OracleCompiler.exists_source_numerical_ready)

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
namespace LogConcaveSampling
open Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal Topology

namespace OracleCompiler

theorem exists_source_numerical_ready {κ J t w : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (ht : 0<t) (hts : t<1/100)
    (hw : 0<w) (hwt : w<t) : ∃n : ℕ,
    J+10<w*((n:ℝ)-3) ∧ J+10<t*((n:ℝ)-3) ∧ 4*(J+10)<(n:ℝ) ∧
    ∀q : ℕ → ℝ,LogPowerRate q (κ*(1/2)) →
      ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,
      SourceShape κ t w n (numericalLayerCount J) d C →
      ∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,0<lam → (lam:ℝ)≤1 →
      ∀hql : q d≤1/4,
      C.MeanNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) hql ∧
      C.SampleNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) := by
  sorry
end OracleCompiler
end LogConcaveSampling

end

end

end OAI
end
