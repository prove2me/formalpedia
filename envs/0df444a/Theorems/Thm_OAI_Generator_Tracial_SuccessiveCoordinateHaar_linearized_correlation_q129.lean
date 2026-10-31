-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_linearized_correlation_q129
-- name    : OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:06:09.645295+00:00
-- url     : https://prove2.me/theorems/83ef7f84-583f-4cd5-8d56-890c812a8ec5
-- title:
--   OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation` of [lean/OAI/Analysis/FactorGeneration/WordCorrelation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/WordCorrelation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge Filter`, `open scoped BigOperators`):
--
--   ```lean
--   theorem SuccessiveCoordinateHaar.linearized_correlation_q129
--       (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (xi : Q τ ω)
--       (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
--       (ell : ℕ) (c : ℂ) :
--       quotientTrace τ ω (star xi*(1+F.firstOrderTerm τ ω u z ell c)*
--         (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=
--         c*(ell : ℂ)*quotientTrace τ ω (star xi*(z : Q τ ω))
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` (definitions bundle `OAIQ129G001` of this split); `OAI.UltrapowerBridge.TracialQuotient`, `OAI.UltrapowerBridge.instStarTracialQuotient`, `OAI.UltrapowerBridge.q129Algebra`, `OAI.UltrapowerBridge.q129One`, `OAI.UltrapowerBridge.q129Semiring` and `OAI.UltrapowerBridge.quotientTrace` (definitions bundle `OAIQ129G004` of this split); `OAI.UltrapowerBridge.q129Add`, `OAI.UltrapowerBridge.q129Mul` and `OAI.Generator.Tracial.Q` (definitions bundle `OAIQ129G008` of this split); `OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient`, `OAI.UltrapowerBridge.q129Monoid` and `OAI.UltrapowerBridge.q129StarRing` (definitions bundle `OAIQ129G009` of this split); `OAI.UltrapowerBridge.q129StarMul`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar` and `OAI.Generator.Tracial.CoordinateHaarData` (definitions bundle `OAIQ129G011` of this split); `OAI.Generator.Tracial.prefixProduct` and `OAI.Generator.Tracial.SuccessiveCoordinateHaar.firstOrderTerm` (definitions bundle `OAIQ129G014` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_correlation_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/WordCorrelation.lean (declaration OAI.Generator.Tracial.SuccessiveCoordinateHaar.linearized_correlation)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ129G014

section

attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator

namespace Tracial

section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge Filter
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.linearized_correlation_q129
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary (Q τ ω)) (xi : Q τ ω)
    (hu : (u : Q τ ω) ∈ seed) (hz : (z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (c : ℂ) :
    quotientTrace τ ω (star xi*(1+F.firstOrderTerm τ ω u z ell c)*
      (prefixProduct τ ω u (fun k => (F.step k).t) (ell+1) : Q τ ω))=
      c*(ell : ℂ)*quotientTrace τ ω (star xi*(z : Q τ ω)) := by
  sorry

end

open UltrapowerBridge

end Tracial

end Generator

end

end OAI
end
