-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_representedCorner_irreducible
-- name    : OAI.Generator.Tracial.representedCorner_irreducible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:52:00.66839+00:00
-- url     : https://prove2.me/theorems/bbc186c6-016d-4e27-b7d3-8f4bb6ebdd26
-- title:
--   OAI.Generator.Tracial.representedCorner_irreducible: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.representedCorner_irreducible` of [lean/OAI/Analysis/FactorGeneration/RepresentedCorners.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/RepresentedCorners.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge`):
--
--   ```lean
--   theorem representedCorner_irreducible (hpN : p.val.val ∈ N) (hNM : N ≤ M)
--       (hirr : ∀ c : M.toStarSubalgebra,
--         (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
--         ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) :
--       ∀ c : (representedCorner p).toStarSubalgebra,
--         (∀ a : (representedSubcorner p hpN).toStarSubalgebra,
--           coordinateInclusion (representedSubcorner_le p hpN hNM) a*c=
--             c*coordinateInclusion (representedSubcorner_le p hpN hNM) a) →
--         ∃ z : ℂ,c=z • (1 : (representedCorner p).toStarSubalgebra)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.Generator.Tracial.coordinateInclusion` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.AlgebraProjection` (definitions bundle `OAIQ11Fg001` of this split); `OAI.Generator.Tracial.cornerSpace` and `OAI.Generator.Tracial.cornerSpace_complete` (definitions bundle `OAIQ11Fg005` of this split); `OAI.Generator.Tracial.representedCorner`, `OAI.Generator.Tracial.representedSubcorner` and `OAI.Generator.Tracial.representedSubcorner_le` (definitions bundle `OAIQ11Fg012` of this split).
--
--   **Used by.** The proofs of `OAI_Generator_Tracial_exists_irreducible_corner_zero_trace_partition`, `OAI.Generator.Tracial.exists_supported_corner_partial_sequence`, `OAI.Generator.Tracial.exists_unitResidual_local_compression`, `OAI_Generator_Tracial_exists_varying_corner_partial_independence` and `OAI.Generator.Tracial.representedCorner_factor` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/RepresentedCorners.lean (declaration OAI.Generator.Tracial.representedCorner_irreducible)

import Mathlib
import Definitions.Def_OAIQ11Fg012

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (p : AlgebraProjection M)

include τ in
theorem representedCorner_irreducible (hpN : p.val.val ∈ N) (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra)) :
    ∀ c : (representedCorner p).toStarSubalgebra,
      (∀ a : (representedSubcorner p hpN).toStarSubalgebra,
        coordinateInclusion (representedSubcorner_le p hpN hNM) a*c=
          c*coordinateInclusion (representedSubcorner_le p hpN hNM) a) →
      ∃ z : ℂ,c=z • (1 : (representedCorner p).toStarSubalgebra) := by
  sorry

end

open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end
