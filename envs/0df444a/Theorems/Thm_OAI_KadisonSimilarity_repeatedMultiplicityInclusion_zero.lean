-- Prove2me | Theorems.Thm_OAI_KadisonSimilarity_repeatedMultiplicityInclusion_zero
-- name    : OAI.KadisonSimilarity.repeatedMultiplicityInclusion_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-03T17:17:56.625875+00:00
-- url     : https://prove2.me/theorems/73995246-8057-4137-9a47-e192d4c36c93
-- title:
--   OAI.KadisonSimilarity.repeatedMultiplicityInclusion_zero: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonSimilarity.repeatedMultiplicityInclusion_zero` of [lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordMultiplicities.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordMultiplicities.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonSimilarity`):
--
--   ```lean
--   theorem repeatedMultiplicityInclusion_zero (ΩA : B) (s : centeredSubspace ΩA)
--       (hs : ‖s‖ = 1) :
--       repeatedMultiplicityInclusion ΩA s hs 0 = (zeroMultiplicityEquiv ΩA).toLinearIsometry
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonSimilarity.CompletedTensorWord`, `OAI.KadisonSimilarity.TensorWord`, `OAI.KadisonSimilarity.centeredSubspace`, `OAI.KadisonSimilarity.hilbertTensorInnerProductSpace`, `OAI.KadisonSimilarity.hilbertTensorNormedAddCommGroup`, `OAI.KadisonSimilarity.tensorWordSpace` and `OAI.KadisonSimilarity.TensorWordSpace` (definitions bundle `OAIQ075A004` of this split); `OAI.KadisonSimilarity.WordMultiplicity`, `OAI.KadisonSimilarity.repeatedMultiplicityInclusion` and `OAI.KadisonSimilarity.zeroMultiplicityEquiv` (definitions bundle `OAIQ075A016` of this split).
--
--   **Used by.** The proof of `OAI.KadisonSimilarity.TracialCornerGeometry.free_corner_estimate_of_published_words` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/KadisonSimilarity/FreeProduct/WordMultiplicities.lean (declaration OAI.KadisonSimilarity.repeatedMultiplicityInclusion_zero)

import Mathlib
import Definitions.Def_OAIQ075A016

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace KadisonSimilarity

universe u
variable {B : Type u} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

variable [CompleteSpace B]

theorem repeatedMultiplicityInclusion_zero (ΩA : B) (s : centeredSubspace ΩA)
    (hs : ‖s‖ = 1) :
    repeatedMultiplicityInclusion ΩA s hs 0 = (zeroMultiplicityEquiv ΩA).toLinearIsometry := by
  sorry

end KadisonSimilarity

end

end OAI
end
