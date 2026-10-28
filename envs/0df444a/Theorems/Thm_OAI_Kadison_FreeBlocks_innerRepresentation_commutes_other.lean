-- Prove2me | Theorems.Thm_OAI_Kadison_FreeBlocks_innerRepresentation_commutes_other
-- name    : OAI.Kadison.FreeBlocks.innerRepresentation_commutes_other
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:36:13.341634+00:00
-- url     : https://prove2.me/theorems/ca0cb0ef-b8a6-4c88-acf8-01380bc222a4
-- title:
--   OAI.Kadison.FreeBlocks.innerRepresentation_commutes_other: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeBlocks`, with `open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator`, `open MeasureTheory MeasureTheory.Measure`, `open FreeWordTensor FreeMoments FreeWordAction`):
--
--   ```lean
--   lemma innerRepresentation_commutes_other (hji : j≠i) (u : unitary D) (a : A) (ha : a∈S j) :
--       (innerRepresentation t ht f S i hS hfree hgen u : t.functional.GNS →L[ℂ] t.functional.GNS)*
--         t.functional.gnsStarAlgHom a = t.functional.gnsStarAlgHom a*
--       (innerRepresentation t ht f S i hS hfree hgen u : t.functional.GNS →L[ℂ] t.functional.GNS)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free` and `OAI.Kadison.FreeWordTensor.FaithfulState` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FreeWordTensor.generatedOperators` (definitions bundle `OAIQ039C036` of this split); `OAI.Kadison.FreeBlocks.innerRepresentation` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.FreeBlocks.exists_free_symmetrization` and `OAI.Kadison.FreeBlocks.innerRepresentation_fixes_baseProjection` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C059

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

lemma innerRepresentation_commutes_other (hji : j≠i) (u : unitary D) (a : A) (ha : a∈S j) :
    (innerRepresentation t ht f S i hS hfree hgen u : t.functional.GNS →L[ℂ] t.functional.GNS)*
      t.functional.gnsStarAlgHom a = t.functional.gnsStarAlgHom a*
    (innerRepresentation t ht f S i hS hfree hgen u : t.functional.GNS →L[ℂ] t.functional.GNS) := by
  sorry

end Kadison.FreeBlocks

end

end
end

end OAI
end
