-- Prove2me | Theorems.Thm_OAI_Kadison_MatrixGNS_flatBalancedUnitary_sq
-- name    : OAI.Kadison.MatrixGNS.flatBalancedUnitary_sq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:44:55.578076+00:00
-- url     : https://prove2.me/theorems/9886aaeb-b5f1-45ad-88f6-6b04263f6900
-- title:
--   OAI.Kadison.MatrixGNS.flatBalancedUnitary_sq: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.MatrixGNS`, with `open scoped BigOperators InnerProductSpace ComplexOrder`):
--
--   ```lean
--   lemma flatBalancedUnitary_sq (X : CStarMatrix ι ι A) (hX : ‖X‖≤1) :
--       (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)*
--         (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)=1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.MatrixGNS.instDecidableEqProd_solutions` (definitions bundle `OAIQ039C013` of this split); `OAI.Kadison.MatrixGNS.flatBalancedUnitary` (definitions bundle `OAIQ039C028` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.MatrixTower.square_contraction_after_average` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C028

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

attribute [local instance] OAI.Kadison.MatrixGNS.instDecidableEqProd_solutions
lemma flatBalancedUnitary_sq (X : CStarMatrix ι ι A) (hX : ‖X‖≤1) :
    (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)*
      (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)=1 := by
  sorry

end Kadison.MatrixGNS

end

end
end

end OAI
end
