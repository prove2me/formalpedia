-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_primitiveBasisFamilyWords_span
-- name    : OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:51:39.951302+00:00
-- url     : https://prove2.me/theorems/c51606ac-5d08-428f-848a-20e80b5752c5
-- title:
--   OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span` of [lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalPBWBasis.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalPBWBasis.lean) at commit 7ef5c0c.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open scoped TensorProduct DirectSum`, the variables of the file, and the hypotheses below):
--
--   ```lean
--   variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
--     [Fact (SlopeEulerSymmetric a c η θ)]
--   variable {J : Type*} [LinearOrder J] (b : J → UnitalShuffle a c η hc θ)
--     (w : J → SlopeWeight c η hc θ)
--     (hw : ∀ i,b i∈globalHomogeneous a c η hc θ (w i))
--     (hp : ∀ i,b i∈globalPrimitives a c η hc θ)
--     (hspan : Submodule.span ℚ (Set.range b)=globalPrimitives a c η hc θ)
--     (hli : LinearIndependent ℚ b)
--
--   include hw hp hspan in
--   lemma primitiveBasisFamilyWords_span :
--       Submodule.span ℚ (Set.range (fun l : PBWWord a c η hc θ (w)=>
--         primitiveWord a c η hc θ (b) l.val))=⊤
--   ```
--
--   **In words.** Under the hypotheses `hw`, `hp` and `hspan`, the statement says that the `ℚ`-span of the set of values `primitiveWord a c η hc θ b l.val`, over the PBW words `l` of `w`, is the whole space `⊤`.
--
--   **Definitions.** The statement uses `UnitalShuffle`, `SlopeWeight`, `globalHomogeneous`, `globalPrimitives`, `PBWWord` and `primitiveWord`, written in the definitions bundles `OAIQ368Chrom040` and `OAIQ368Chrom048` of this split.
--
--   **Used by.** The proof files of `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds` and `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/GlobalPBWBasis.lean (declaration OAI.ElementaryPositivity.RawShuffle.primitiveBasisFamilyWords_span)

import Mathlib
import Definitions.Def_OAIQ368Chrom040

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable Classical.decEq
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J] (b : J → UnitalShuffle a c η hc θ)
  (w : J → SlopeWeight c η hc θ)
  (hw : ∀ i,b i∈globalHomogeneous a c η hc θ (w i))
  (hp : ∀ i,b i∈globalPrimitives a c η hc θ)
  (hspan : Submodule.span ℚ (Set.range b)=globalPrimitives a c η hc θ)
  (hli : LinearIndependent ℚ b)

include hw hp hspan in
lemma primitiveBasisFamilyWords_span :
    Submodule.span ℚ (Set.range (fun l : PBWWord a c η hc θ (w)=>
      primitiveWord a c η hc θ (b) l.val))=⊤ := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
