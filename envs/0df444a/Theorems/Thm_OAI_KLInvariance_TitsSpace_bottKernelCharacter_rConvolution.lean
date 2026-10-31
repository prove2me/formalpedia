-- Prove2me | Theorems.Thm_OAI_KLInvariance_TitsSpace_bottKernelCharacter_rConvolution
-- name    : OAI.KLInvariance.TitsSpace.bottKernelCharacter_rConvolution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:56:47.890986+00:00
-- url     : https://prove2.me/theorems/0c46d09e-8d0f-44fa-8825-bc7b6d63dd7d
-- title:
--   OAI.KLInvariance.TitsSpace.bottKernelCharacter_rConvolution: intermediate lemma from OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KLInvariance.TitsSpace.bottKernelCharacter_rConvolution` of [lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KLInvariance.TitsSpace`, with `open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph Polynomial`):
--
--   ```lean
--   theorem bottKernelCharacter_rConvolution (l : List I) (hl : cs.IsReduced l)
--       (x : Interval cs 1 (cs.wordProd l)) :
--       GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
--         (bottKernelFree cs basis l hl) x=
--         ∑ z : Interval cs 1 (cs.wordProd l),
--           OrdinaryR.polynomial cs x.val z.val*bottStalkCharacter cs basis l z.val
--   ```
--
--   **Definitions.** The statement is written with `OAI.KLInvariance.BruhatGraph.Edge`, `OAI.KLInvariance.BruhatGraph.graph`, `OAI.KLInvariance.TitsSpace.Extended` and `OAI.KLInvariance.TitsSpace.form` (definitions bundle `OAIQ124K000` of this split); `OAI.KLInvariance.TitsSpace.rWordInterval` (definitions bundle `OAIQ124K007` of this split); `OAI.KLInvariance.OrdinaryR.polynomial` and `OAI.KLInvariance.MomentGraph.GradedSheaf.freeKernelChar` (definitions bundle `OAIQ124K011` of this split); `OAI.KLInvariance.TitsSpace.bottPolynomialSheaf` (definitions bundle `OAIQ124K018` of this split); `OAI.KLInvariance.TitsSpace.bottKernelFree` and `OAI.KLInvariance.TitsSpace.bottStalkCharacter` (definitions bundle `OAIQ124K023` of this split); `OAI.KLInvariance.BruhatLE`, `OAI.KLInvariance.Interval` and `OAI.KLInvariance.intervalOrder` (the published bundle `Def_KLInvariance`).
--
--   **Used by.** The proof of `OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper` of this split imports it.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean (declaration OAI.KLInvariance.TitsSpace.bottKernelCharacter_rConvolution)

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K023

section

attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 local instance charDecEqB_rdf48a3_1 (a : Type*) : DecidableEq a := Classical.decEq a
local instance rWordEdges_rdf48a3_1 (l : List I) : Fintype (Edge cs 1 (cs.wordProd l)) := Fintype.ofFinite _
attribute [local instance] OAI.KLInvariance.TitsSpace.rWordInterval
theorem bottKernelCharacter_rConvolution (l : List I) (hl : cs.IsReduced l)
    (x : Interval cs 1 (cs.wordProd l)) :
    GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
      (bottKernelFree cs basis l hl) x=
      ∑ z : Interval cs 1 (cs.wordProd l),
        OrdinaryR.polynomial cs x.val z.val*bottStalkCharacter cs basis l z.val := by
  sorry

end
end KLInvariance.TitsSpace

end

end OAI
end
