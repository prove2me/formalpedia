-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_reduced_integer_moment_closedSpan
-- name    : OAI.Generator.Tracial.reduced_integer_moment_closedSpan
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T10:56:11.988867+00:00
-- url     : https://prove2.me/theorems/51b89d14-ec3d-4f35-a62b-ad8110de498a
-- title:
--   OAI.Generator.Tracial.reduced_integer_moment_closedSpan: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.reduced_integer_moment_closedSpan` of [lean/OAI/Analysis/FactorGeneration/LaurentMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LaurentMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem reduced_integer_moment_closedSpan (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
--       (hm : ReducedOrderedMoments τ ω (v : Q τ ω) x)
--       (a b : Q τ ω)
--       (ha : a ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
--       (hb : b ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
--       (n : ℤ) (hn : n ≠ 0) (xs : List (Q τ ω × ℤ))
--       (hxs : ∀ z ∈ xs,z.1 ∈ traceClosedSpan τ ω (Set.range x) ∧ z.2 ≠ 0) :
--       quotientTrace τ ω (a*integerValueWord τ ω v n xs b)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.UltrapowerBridge.quotientTrace` and `OAI.UltrapowerBridge.traceCongruence` (definitions bundle `OAIQ11Fg000` of this split); `OAI.UltrapowerBridge.instStarRingTracialQuotient` (definitions bundle `OAIQ11Fg004` of this split); `OAI.Generator.Tracial.Q` (definitions bundle `OAIQ11Fg007` of this split); `OAI.Generator.Tracial.quotientInnerProductSpace` and `OAI.Generator.Tracial.quotientNormedAddCommGroup` (definitions bundle `OAIQ11Fg011` of this split); `OAI.Generator.Tracial.ReducedOrderedMoments` (definitions bundle `OAIQ11Fg014` of this split); `OAI.Generator.Tracial.integerValueWord` (definitions bundle `OAIQ11Fg020` of this split); `OAI.Generator.Tracial.traceClosedSpan` (definitions bundle `OAIQ11Fg023` of this split).
--
--   **Used by.** The proofs of `OAI_Generator_Tracial_exists_coordinate_haar_endpoints` and `OAI.Generator.Tracial.nonempty_coordinateHaarData` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LaurentMoments.lean (declaration OAI.Generator.Tracial.reduced_integer_moment_closedSpan)

import Mathlib
import Definitions.Def_OAIQ11Fg023

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial

section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem reduced_integer_moment_closedSpan (v : unitary (Q τ ω)) (x : ℕ → Q τ ω)
    (hm : ReducedOrderedMoments τ ω (v : Q τ ω) x)
    (a b : Q τ ω)
    (ha : a ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
    (hb : b ∈ traceClosedSpan τ ω (insert 1 (Set.range x)))
    (n : ℤ) (hn : n ≠ 0) (xs : List (Q τ ω × ℤ))
    (hxs : ∀ z ∈ xs,z.1 ∈ traceClosedSpan τ ω (Set.range x) ∧ z.2 ≠ 0) :
    quotientTrace τ ω (a*integerValueWord τ ω v n xs b)=0 := by
  sorry

end

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end
