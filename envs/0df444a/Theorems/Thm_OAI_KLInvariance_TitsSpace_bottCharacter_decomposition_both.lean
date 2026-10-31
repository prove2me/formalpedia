-- Prove2me | Theorems.Thm_OAI_KLInvariance_TitsSpace_bottCharacter_decomposition_both
-- name    : OAI.KLInvariance.TitsSpace.bottCharacter_decomposition_both
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:01:53.871712+00:00
-- url     : https://prove2.me/theorems/5c4554fb-5003-42bc-90dd-8d781b2eedd5
-- title:
--   OAI.KLInvariance.TitsSpace.bottCharacter_decomposition_both: intermediate lemma from OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KLInvariance.TitsSpace.bottCharacter_decomposition_both` of [lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KLInvariance.TitsSpace`, with `open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph Polynomial`):
--
--   ```lean
--    theorem bottCharacter_decomposition_both (l : List I) (hl : cs.IsReduced l)
--       [Fintype (Interval cs 1 (cs.wordProd l))] :
--       ∃ m : Interval cs 1 (cs.wordProd l) → Polynomial ℤ,
--         (∀ y n, 0≤(m y).coeff n) ∧
--         (∀ x, bottStalkCharacter cs basis l x.val=
--           ∑ y, m y*lowerCharacter cs (cs.wordProd l) basis y x) ∧
--         (∀ x, GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
--           (bottKernelFree cs basis l hl) x=
--           ∑ y, m y*Polynomial.reflect (rankDifference cs x.val y.val)
--             (lowerCharacter cs (cs.wordProd l) basis y x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.KLInvariance.BruhatGraph.Edge`, `OAI.KLInvariance.BruhatGraph.graph`, `OAI.KLInvariance.TitsSpace.Extended` and `OAI.KLInvariance.TitsSpace.form` (definitions bundle `OAIQ124K000` of this split); `OAI.KLInvariance.BruhatGraph.lowerCharacter` and `OAI.KLInvariance.MomentGraph.GradedSheaf.freeKernelChar` (definitions bundle `OAIQ124K011` of this split); `OAI.KLInvariance.TitsSpace.bottPolynomialSheaf` (definitions bundle `OAIQ124K018` of this split); `OAI.KLInvariance.TitsSpace.bottKernelFree` and `OAI.KLInvariance.TitsSpace.bottStalkCharacter` (definitions bundle `OAIQ124K023` of this split); `OAI.KLInvariance.BruhatLE`, `OAI.KLInvariance.Interval`, `OAI.KLInvariance.intervalOrder` and `OAI.KLInvariance.rankDifference` (the published bundle `Def_KLInvariance`).
--
--   **Used by.** The proof of `OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper` of this split imports it.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean (declaration OAI.KLInvariance.TitsSpace.bottCharacter_decomposition_both)

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

 theorem bottCharacter_decomposition_both (l : List I) (hl : cs.IsReduced l)
    [Fintype (Interval cs 1 (cs.wordProd l))] :
    ∃ m : Interval cs 1 (cs.wordProd l) → Polynomial ℤ,
      (∀ y n, 0≤(m y).coeff n) ∧
      (∀ x, bottStalkCharacter cs basis l x.val=
        ∑ y, m y*lowerCharacter cs (cs.wordProd l) basis y x) ∧
      (∀ x, GradedSheaf.freeKernelChar (bottPolynomialSheaf cs basis l 1 (cs.wordProd l))
        (bottKernelFree cs basis l hl) x=
        ∑ y, m y*Polynomial.reflect (rankDifference cs x.val y.val)
          (lowerCharacter cs (cs.wordProd l) basis y x)) := by
  sorry

end
end KLInvariance.TitsSpace

end

end OAI
end
