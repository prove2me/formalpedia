-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_representedCorner_irreducible_q129
-- name    : OAI.Generator.Tracial.representedCorner_irreducible_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:25:39.454409+00:00
-- url     : https://prove2.me/theorems/53b09c64-1276-49cf-8945-8ff2e49cb09b
-- title:
--   OAI.Generator.Tracial.representedCorner_irreducible_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.representedCorner_irreducible` of [lean/OAI/Analysis/FactorGeneration/RepresentedCorners.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/RepresentedCorners.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge`):
--
--   ```lean
--   theorem representedCorner_irreducible_q129 (hpN : p.val.val ∈ N) (hNM : N ≤ M)
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
--   **Definitions.** The statement is written with `OAI.Generator.Tracial.AlgebraProjection` (definitions bundle `OAIQ129G000` of this split); `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.Generator.Tracial.coordinateInclusion` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.Tracial.cornerSpace`, `OAI.Generator.Tracial.cornerSpace_complete`, `OAI.Generator.Tracial.representedCorner`, `OAI.Generator.Tracial.representedSubcorner` and `OAI.Generator.Tracial.representedSubcorner_le` (definitions bundle `OAIQ129G005` of this split).
--
--   **Used by.** The proofs of `OAI.Generator.Tracial.exists_exact_residual_iteration_q129`, `OAI_Generator_Tracial_exists_quotient_corner_partial_sequence_q129`, `OAI.Generator.Tracial.exists_unitResidual_local_compression_q129` and `OAI.Generator.Tracial.representedCorner_factor_q129` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/RepresentedCorners.lean (declaration OAI.Generator.Tracial.representedCorner_irreducible)

import Mathlib
import Definitions.Def_OAIQ129G005

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator.Tracial

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (p : AlgebraProjection M)

include τ in
theorem representedCorner_irreducible_q129 (hpN : p.val.val ∈ N) (hNM : N ≤ M)
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
