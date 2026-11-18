-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_globalCoproduct_mul
-- name    : OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:45:37.501939+00:00
-- url     : https://prove2.me/theorems/237ca845-32f9-43d0-bd22-af43bb52df74
-- title:
--   OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul` of [lean/OAI/Combinatorics/Chromatic/Shuffle/SlopeGridSum.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/SlopeGridSum.lean) at commit 7ef5c0c.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit` and `open scoped TensorProduct DirectSum`):
--
--   ```lean
--   theorem globalCoproduct_mul (a : I → I → ℕ) (c η : I → ℝ)
--       (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
--       (x y : UnitalShuffle a c η hc θ) :
--       globalCoproduct a c η hc θ (x*y)=
--         globalSignedTensorMultiply a c η hc θ
--           (globalCoproduct a c η hc θ x) (globalCoproduct a c η hc θ y)
--   ```
--
--   **In words.** The statement says that the global coproduct of the product `x*y` equals the global signed tensor multiply of the global coproducts of `x` and `y`.
--
--   **Definitions.** The statement uses `globalCoproduct`, `globalSignedTensorMultiply`, `UnitalShuffle` and `SlopeEulerSymmetric`, written in the definitions bundle `OAIQ368Chrom035` of this split.
--
--   **Used by.** The proof files of `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_independent` and `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/SlopeGridSum.lean (declaration OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul)

import Mathlib
import Definitions.Def_OAIQ368Chrom035

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

theorem globalCoproduct_mul (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) [Fact (SlopeEulerSymmetric a c η θ)]
    (x y : UnitalShuffle a c η hc θ) :
    globalCoproduct a c η hc θ (x*y)=
      globalSignedTensorMultiply a c η hc θ
        (globalCoproduct a c η hc θ x) (globalCoproduct a c η hc θ y) := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
