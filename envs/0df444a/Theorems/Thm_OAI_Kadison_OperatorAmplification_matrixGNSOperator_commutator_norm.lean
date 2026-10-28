-- Prove2me | Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixGNSOperator_commutator_norm
-- name    : OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutator_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:49:57.308112+00:00
-- url     : https://prove2.me/theorems/7df6eaa3-bf05-4622-9ead-1c49b17e65f5
-- title:
--   OAI.Kadison.OperatorAmplification.matrixGNSOperator_commutator_norm: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.OperatorAmplification`, with `open scoped BigOperators InnerProductSpace ComplexOrder`):
--
--   ```lean
--   lemma matrixGNSOperator_commutator_norm
--       (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
--       (X : CStarMatrix ι ι M) :
--       ‖matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X-
--         (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X*matrixGNSOperator ι M τ T‖=
--       ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T*MatrixGNS.representation τ X-
--         MatrixGNS.representation τ X*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.diagonal` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.MatrixGNS.ArraySpace` and `OAI.Kadison.MatrixGNS.matrixVectorTraceDecidableEq` (definitions bundle `OAIQ039C013` of this split); `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_3` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.MatrixGNS.representation` (definitions bundle `OAIQ039C039` of this split); `OAI.Kadison.MatrixGNS.trace` (definitions bundle `OAIQ039C061` of this split); `OAI.Kadison.OperatorAmplification.matrixGNSOperator` (definitions bundle `OAIQ039C067` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.OperatorAmplification.matrixGNSOperator_small_corner` and `OAI.Kadison.OperatorAmplification.matrix_free_symmetry_bound` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C067

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_3
variable (τ : M →ₚ[ℂ] ℂ)

lemma matrixGNSOperator_commutator_norm
    (T : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : CStarMatrix ι ι M) :
    ‖matrixGNSOperator ι M τ T*(MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X-
      (MatrixGNS.trace (ι:=ι) τ).gnsStarAlgHom X*matrixGNSOperator ι M τ T‖=
    ‖diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T*MatrixGNS.representation τ X-
      MatrixGNS.representation τ X*diagonal (H:=SumSpace (H:=τ.GNS) ι) ι T‖ := by
  sorry

end Kadison.OperatorAmplification

end

end
end

end OAI
end
