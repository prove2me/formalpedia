-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_double_embedding_small
-- name    : OAI.Kadison.TracialSequence.double_embedding_small
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:43:16.336965+00:00
-- url     : https://prove2.me/theorems/57292271-5bc9-46fa-a801-be127983d543
-- title:
--   OAI.Kadison.TracialSequence.double_embedding_small: OpenAI's double_embedding with its left side named (Kadison's similarity theorem, result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`: OpenAI's lemma `OAI.Kadison.TracialSequence.double_embedding` (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0; declaration `double_embedding` of [lean/OAI/Analysis/Commutator/Commutator/TracialDoubleCompression.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Commutator/Commutator/TracialDoubleCompression.lean) at commit adc7f12), with its left side written as `OAI.Kadison.TracialSequence.doubleEmbeddingLeft` (definitions bundle `OAIQ039D000`), an abbreviation for exactly OpenAI's term. It says the same as the published `OAI.Kadison.TracialSequence.double_embedding`, whose statement module the platform cannot build within 300 s (its type is about $1.3 \cdot 10^9$ nodes written out without sharing); this form has a small type.
--
--   **The statement** (namespace `OAI.Kadison.TracialSequence`, with `open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction`, `open Filter UniformSpace ContinuousLinearMap`, `open TracialGNS FreeWordTensor FreeBlocks`):
--
--   ```lean
--   theorem double_embedding_small {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
--       (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
--       (M : VonNeumannAlgebra (boundedSubspace τ ω))
--       (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
--       (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
--       (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
--         Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
--       (hone : τ 1=1) (x : τ.GNS) :
--       doubleEmbeddingLeft τ ω M hconst hτ hM hone x=constantIn τ ω x
--   ```
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.double_compression_preserves_small` imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Commutator/Commutator/TracialDoubleCompression.lean (declaration OAI.Kadison.TracialSequence.double_embedding)

import Mathlib
import Definitions.Def_OAIQ039D000

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter UniformSpace ContinuousLinearMap

namespace Kadison.TracialSequence

open TracialGNS FreeWordTensor FreeBlocks

theorem double_embedding_small {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hone : τ 1=1) (x : τ.GNS) :
    doubleEmbeddingLeft τ ω M hconst hτ hM hone x=constantIn τ ω x := by
  sorry

end Kadison.TracialSequence

end

end OAI

end
