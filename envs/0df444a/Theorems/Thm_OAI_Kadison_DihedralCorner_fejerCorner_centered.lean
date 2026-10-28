-- Prove2me | Theorems.Thm_OAI_Kadison_DihedralCorner_fejerCorner_centered
-- name    : OAI.Kadison.DihedralCorner.fejerCorner_centered
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:33:05.84806+00:00
-- url     : https://prove2.me/theorems/fcb9710d-44fb-46a9-bc99-e50c6c2cb6d7
-- title:
--   OAI.Kadison.DihedralCorner.fejerCorner_centered: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.DihedralCorner`, with `open scoped BigOperators ComplexOrder`, `open FreeMoments FejerTest`):
--
--   ```lean
--   lemma fejerCorner_centered (m : ℕ) (hm : 0 < m) :
--       halfCornerTrace hp φ.toLinearMap (fejerCorner hp (d*s) m)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.Corner`, `OAI.Kadison.instModuleComplexCorner` and `OAI.Kadison.instRingCorner` (definitions bundle `OAIQ039C004` of this split); `OAI.Kadison.FreeMoments.Free` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.halfCornerTrace` (definitions bundle `OAIQ039C054` of this split); `OAI.Kadison.DihedralCorner.fejerCorner` (definitions bundle `OAIQ039C059` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.FreeBlocks.finite_fejer_entry` and `OAI.Kadison.FreeBlocks.free_fejer_norm` of this split import it.
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

open scoped BigOperators ComplexOrder

namespace Kadison.DihedralCorner

open FreeMoments FejerTest

variable {A : Type*} [CStarAlgebra A]

variable {p : A} (hp : IsStarProjection p)

variable [PartialOrder A] [StarOrderedRing A]

variable (φ : A →ₚ[ℂ] ℂ) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (h1 : φ 1=1) (htr : ∀ a b : A, φ (a*b)=φ (b*a))
  (hstar : ∀ a : A, φ (star a)=star (φ a)) (hfree : Free S φ.toLinearMap)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d:A)∈S i) (hs : (s:A)∈S j)
  (hd0 : φ (d:A)=0) (hs0 : φ (s:A)=0)

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d:A)*(d:A)=1)

variable (hpform : p=(1/2:ℂ) • (1+(d:A)))

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hr hpform in
omit [StarOrderedRing A] in
lemma fejerCorner_centered (m : ℕ) (hm : 0 < m) :
    halfCornerTrace hp φ.toLinearMap (fejerCorner hp (d*s) m)=0 := by
  sorry

end Kadison.DihedralCorner

end

end
end

end OAI
end
