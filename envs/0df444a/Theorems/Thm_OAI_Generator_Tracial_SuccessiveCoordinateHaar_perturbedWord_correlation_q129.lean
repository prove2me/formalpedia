-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_perturbedWord_correlation_q129
-- name    : OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord_correlation_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:15:45.468974+00:00
-- url     : https://prove2.me/theorems/f302c4fb-cbde-428c-8268-298589035347
-- title:
--   OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord_correlation_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord_correlation` of [lean/OAI/Analysis/FactorGeneration/WordCorrelation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/WordCorrelation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge`):
--
--   ```lean
--   theorem SuccessiveCoordinateHaar.perturbedWord_correlation_q129
--       (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
--       (xi : Q τ ω)
--       (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
--       (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
--       (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
--       ‖quotientTrace τ ω (star xi*sequenceQuotient τ ω
--           (F.perturbedWord τ ω u z ell α : Sequences M))-
--         (α : ℂ)/2*quotientTrace τ ω (star xi*(constantQuotientUnitary τ ω z : Q τ ω))‖ ≤
--           ‖xi‖*(4*α^2/(1-2*α))
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.Generator.Tracial.Sequences` (definitions bundle `OAIQ129G001` of this split); `OAI.UltrapowerBridge.instStarTracialQuotient`, `OAI.UltrapowerBridge.q129Algebra`, `OAI.UltrapowerBridge.q129Semiring` and `OAI.UltrapowerBridge.quotientTrace` (definitions bundle `OAIQ129G004` of this split); `OAI.UltrapowerBridge.q129Mul` and `OAI.Generator.Tracial.Q` (definitions bundle `OAIQ129G008` of this split); `OAI.UltrapowerBridge.q129Monoid` (definitions bundle `OAIQ129G009` of this split); `OAI.UltrapowerBridge.q129StarMul`, `OAI.Generator.Tracial.SuccessiveCoordinateHaar`, `OAI.Generator.Tracial.quotientNormedAddCommGroup` and `OAI.Generator.Tracial.sequenceQuotient` (definitions bundle `OAIQ129G011` of this split); `OAI.Generator.Tracial.constantQuotientUnitary` and `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord` (definitions bundle `OAIQ129G014` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.represented_relative_generation_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/WordCorrelation.lean (declaration OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord_correlation)

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

open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.perturbedWord_correlation_q129
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (xi : Q τ ω)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed) (hxi : xi ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ‖quotientTrace τ ω (star xi*sequenceQuotient τ ω
        (F.perturbedWord τ ω u z ell α : Sequences M))-
      (α : ℂ)/2*quotientTrace τ ω (star xi*(constantQuotientUnitary τ ω z : Q τ ω))‖ ≤
        ‖xi‖*(4*α^2/(1-2*α)) := by
  sorry

end Tracial

end Generator

end

end OAI
end
