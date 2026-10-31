-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_SuccessiveCoordinateHaar_exponential_product_eq_word
-- name    : OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_eq_word
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T11:04:09.194792+00:00
-- url     : https://prove2.me/theorems/cb09a991-7bef-454e-a78d-5215a0dcd343
-- title:
--   OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_eq_word: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_eq_word` of [lean/OAI/Analysis/FactorGeneration/WordCorrelation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/WordCorrelation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge`):
--
--   ```lean
--   theorem SuccessiveCoordinateHaar.exponential_product_eq_word
--       (F : SuccessiveCoordinateHaar τ ω hNM seed)
--       (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) :
--       ((finitePerturbationRows ell α).map
--         (fun r => NormedSpace.exp (F.perturbationMap τ ω u z ell r))).prod*
--         (F.coordinatePrefix τ ω u (ell+1) : Sequences M)=
--           (F.perturbedWord τ ω u z ell α : Sequences M)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.PrefixLabel` (definitions bundle `OAIQ11Fg001` of this split); `OAI.Generator.Tracial.Sequences` and `OAI.Generator.Tracial.sequencesIsTopologicalRing` (definitions bundle `OAIQ11Fg002` of this split); `OAI.Generator.Tracial.Q` (definitions bundle `OAIQ11Fg007` of this split); `OAI.Generator.finitePerturbationRows` (definitions bundle `OAIQ11Fg010` of this split); `OAI.Generator.Tracial.SuccessiveCoordinateHaar` and `OAI.Generator.Tracial.SuccessiveCoordinateHaar.coordinatePrefix` (definitions bundle `OAIQ11Fg015` of this split); `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbationMap` and `OAI.Generator.Tracial.SuccessiveCoordinateHaar.perturbedWord` (definitions bundle `OAIQ11Fg017` of this split).
--
--   **Used by.** The proofs of `OAI_Generator_Tracial_SuccessiveCoordinateHaar_perturbedWord_correlation` and `OAI.Generator.Tracial.SuccessiveCoordinateHaar.select_perturbation_coordinate` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/WordCorrelation.lean (declaration OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_eq_word)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ11Fg017

section

attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator

namespace Tracial

section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem SuccessiveCoordinateHaar.exponential_product_eq_word
    (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (u z : unitary M.toStarSubalgebra) (ell : ℕ) (α : ℝ) :
    ((finitePerturbationRows ell α).map
      (fun r => NormedSpace.exp (F.perturbationMap τ ω u z ell r))).prod*
      (F.coordinatePrefix τ ω u (ell+1) : Sequences M)=
        (F.perturbedWord τ ω u z ell α : Sequences M) := by
  sorry

end

open UltrapowerBridge

end Tracial

end Generator

end

end OAI
end
