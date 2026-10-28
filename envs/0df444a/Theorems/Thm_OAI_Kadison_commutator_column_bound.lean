-- Prove2me | Theorems.Thm_OAI_Kadison_commutator_column_bound
-- name    : OAI.Kadison.commutator_column_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:22:23.723616+00:00
-- url     : https://prove2.me/theorems/01308b60-e65a-45ba-a740-01f0ac9789d5
-- title:
--   OAI.Kadison.commutator_column_bound: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped InnerProductSpace BigOperators`):
--
--   ```lean
--   lemma commutator_column_bound (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
--       (h : ℕ) (a : Fin h → P) (ha : CyclicColumns.columnNorm a≤1) :
--       ‖operatorColumn h (fun i => Y*(a i : K →L[ℂ] K)-(a i : K →L[ℂ] K)*Y)‖ ≤
--         4*commutatorSeminorm P Y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.VonNeumannCStar.starOrderedRing` (definitions bundle `OAIQ039C003` of this split); `OAI.Kadison.CyclicColumns.columnNorm` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.operatorColumn` (definitions bundle `OAIQ039C019` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.commutatorSeminorm` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proof of `OAI.Kadison.isometry_column_error_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C022

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma commutator_column_bound (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
    (h : ℕ) (a : Fin h → P) (ha : CyclicColumns.columnNorm a≤1) :
    ‖operatorColumn h (fun i => Y*(a i : K →L[ℂ] K)-(a i : K →L[ℂ] K)*Y)‖ ≤
      4*commutatorSeminorm P Y := by
  sorry

end Kadison

end

end
end

end OAI
end
