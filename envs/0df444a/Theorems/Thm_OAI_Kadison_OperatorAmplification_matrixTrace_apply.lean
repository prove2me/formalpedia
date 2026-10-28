-- Prove2me | Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_apply
-- name    : OAI.Kadison.OperatorAmplification.matrixTrace_apply
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:51:40.162315+00:00
-- url     : https://prove2.me/theorems/7801a487-3851-4654-83bb-713fc03a8994
-- title:
--   OAI.Kadison.OperatorAmplification.matrixTrace_apply: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.OperatorAmplification`, with `open scoped BigOperators InnerProductSpace ComplexOrder Topology`, `open ContinuousLinearMapWOT`):
--
--   ```lean
--   lemma matrixTrace_apply (T : matrixVonNeumann ι i₀ M) :
--       matrixTrace ι i₀ M τ T=(Fintype.card ι : ℂ)⁻¹ * ∑ i,
--         τ ⟨entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i i,
--           (mem_matrixVonNeumann ι i₀ M T).mp T.property i i⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.OperatorAmplification.SumSpace` and `OAI.Kadison.OperatorAmplification.entry` (definitions bundle `OAIQ039C002` of this split); `OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_1` (definitions bundle `OAIQ039C014` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.OperatorAmplification.matrixVonNeumann` and `OAI.Kadison.OperatorAmplification.mem_matrixVonNeumann` (definitions bundle `OAIQ039C050` of this split); `OAI.Kadison.OperatorAmplification.matrixTrace` (definitions bundle `OAIQ039C068` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.OperatorAmplification.matrixTrace_diagonal`, `OAI.Kadison.OperatorAmplification.matrixTrace_normal` and `OAI.Kadison.OperatorAmplification.matrixTrace_restrict` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C068

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

open scoped BigOperators InnerProductSpace ComplexOrder Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_1
variable (τ : M →ₚ[ℂ] ℂ)

lemma matrixTrace_apply (T : matrixVonNeumann ι i₀ M) :
    matrixTrace ι i₀ M τ T=(Fintype.card ι : ℂ)⁻¹ * ∑ i,
      τ ⟨entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i i,
        (mem_matrixVonNeumann ι i₀ M T).mp T.property i i⟩ := by
  sorry

end Kadison.OperatorAmplification

end

end
end

end OAI
end
