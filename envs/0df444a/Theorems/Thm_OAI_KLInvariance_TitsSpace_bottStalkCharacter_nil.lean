-- Prove2me | Theorems.Thm_OAI_KLInvariance_TitsSpace_bottStalkCharacter_nil
-- name    : OAI.KLInvariance.TitsSpace.bottStalkCharacter_nil
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:01:45.90697+00:00
-- url     : https://prove2.me/theorems/66d0267c-6ec7-450e-a542-1f1765ca5d6d
-- title:
--   OAI.KLInvariance.TitsSpace.bottStalkCharacter_nil: intermediate lemma from OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KLInvariance.TitsSpace.bottStalkCharacter_nil` of [lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KLInvariance.TitsSpace`, with `open Module _root_.OAI.KLInvariance.Graded`):
--
--   ```lean
--   theorem bottStalkCharacter_nil (x : W) :
--       bottStalkCharacter cs basis [] x=if x=1 then 1 else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.KLInvariance.TitsSpace.Extended` and `OAI.KLInvariance.TitsSpace.form` (definitions bundle `OAIQ124K000` of this split); `OAI.KLInvariance.TitsSpace.instDecidable_solutions_7` (definitions bundle `OAIQ124K003` of this split); `OAI.KLInvariance.TitsSpace.bottStalkCharacter` (definitions bundle `OAIQ124K023` of this split).
--
--   **Used by.** The proof of `OAI.KLInvariance.TitsSpace.bottKernelCharacter_rConvolution` of this split imports it.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean (declaration OAI.KLInvariance.TitsSpace.bottStalkCharacter_nil)

import Mathlib
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
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_7
theorem bottStalkCharacter_nil (x : W) :
    bottStalkCharacter cs basis [] x=if x=1 then 1 else 0 := by
  sorry

end
end KLInvariance.TitsSpace

end

end OAI
end
