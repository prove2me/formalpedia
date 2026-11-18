-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_stringPBWBasis_component
-- name    : OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T19:49:09.205041+00:00
-- url     : https://prove2.me/theorems/5e3b21d8-007d-4239-b4a6-2535ed6099bf
-- title:
--   OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component` of [lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalHilbertGrading.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalHilbertGrading.lean) at commit 7ef5c0c.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open scoped DirectSum` and `variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)` with `[Fact (SlopeEulerSymmetric a c η θ)]`):
--
--   ```lean
--   lemma stringPBWBasis_component (k : SlopeWeight c η hc θ ×ℤ) (l : StringPBWIndex a c η hc θ) :
--       globalOriginalComponent a c η hc θ k.1 k.2 (globalStringPBWBasis a c η hc θ l)=
--         if stringPBWGrade a c η hc θ l=k then globalStringPBWBasis a c η hc θ l else 0
--   ```
--
--   **In words.** For a grade `k` (a pair in `SlopeWeight c η hc θ ×ℤ`) and an index `l` of `StringPBWIndex`, the statement says that `globalOriginalComponent` at `k.1` and `k.2`, applied to `globalStringPBWBasis l`, equals `globalStringPBWBasis l` when `stringPBWGrade l = k`, and equals `0` otherwise.
--
--   **Definitions.** The statement uses `SlopeWeight`, `StringPBWIndex`, `globalOriginalComponent`, `globalStringPBWBasis` and `stringPBWGrade`, written in the definitions bundles `OAIQ368Chrom051` and `OAIQ368Chrom053` of this split.
--
--   **Used by.** Its proof file imports the published statements `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_independent` and `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalHilbertGrading.lean (declaration OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component)

import Mathlib
import Definitions.Def_OAIQ368Chrom051
import Definitions.Def_OAIQ368Chrom053

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

lemma stringPBWBasis_component (k : SlopeWeight c η hc θ ×ℤ) (l : StringPBWIndex a c η hc θ) :
    globalOriginalComponent a c η hc θ k.1 k.2 (globalStringPBWBasis a c η hc θ l)=
      if stringPBWGrade a c η hc θ l=k then globalStringPBWBasis a c η hc θ l else 0 := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
