-- Prove2me | Theorems.Thm_OAI_Kadison_CyclicSpatial_matrixRepresentation_norm_eq
-- name    : OAI.Kadison.CyclicSpatial.matrixRepresentation_norm_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:34.404678+00:00
-- url     : https://prove2.me/theorems/5af64f12-35a9-4f7f-b65e-aa1476df0798
-- title:
--   OAI.Kadison.CyclicSpatial.matrixRepresentation_norm_eq: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CyclicSpatial`, with `open scoped BigOperators InnerProductSpace`, `open OperatorAmplification CyclicColumns ReducingRepresentation`):
--
--   ```lean
--   lemma matrixRepresentation_norm_eq (lam : A →⋆ₐ[ℂ] (H →L[ℂ] H))
--       (hlam : Function.Injective lam) (X : CStarMatrix ι ι A) :
--       ‖matrixRepresentation lam X‖=‖X‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CyclicColumns.instDecidableEq_solutions` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.CyclicColumns.matrixRepresentation` (definitions bundle `OAIQ039C022` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner`, `OAI.Kadison.MatrixTower.finite_standard_gauge_bound` and `OAI.Kadison.matrixOperator_subtype_norm_le` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.CyclicSpatial

open OperatorAmplification CyclicColumns ReducingRepresentation

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

lemma matrixRepresentation_norm_eq (lam : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hlam : Function.Injective lam) (X : CStarMatrix ι ι A) :
    ‖matrixRepresentation lam X‖=‖X‖ := by
  sorry

end Kadison.CyclicSpatial

end

end
end

end OAI
end
