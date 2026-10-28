-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_double_compression_preserves_small
-- name    : OAI.Kadison.TracialSequence.double_compression_preserves_small
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:43:13.48829+00:00
-- url     : https://prove2.me/theorems/5b580b8d-78bd-4aea-97e3-07d00970fc85
-- title:
--   OAI.Kadison.TracialSequence.double_compression_preserves_small: OpenAI's double_compression_preserves with both sides named (Kadison's similarity theorem, result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`: OpenAI's lemma `OAI.Kadison.TracialSequence.double_compression_preserves` (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0; declaration `double_compression_preserves` of [lean/OAI/Analysis/Commutator/Commutator/TracialDoubleCompression.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Commutator/Commutator/TracialDoubleCompression.lean) at commit adc7f12), with its two sides written as `OAI.Kadison.TracialSequence.doubleCompressionLeft` and `OAI.Kadison.TracialSequence.doubleCompressionRight` (definitions bundle `OAIQ039D000`), abbreviations for exactly OpenAI's terms. It says the same as the published `OAI.Kadison.TracialSequence.double_compression_preserves`, whose statement module the platform cannot build within 300 s (its type is about $2.6 \cdot 10^9$ nodes written out without sharing); this form has a small type.
--
--   **The statement** (namespace `OAI.Kadison.TracialSequence`, with `open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction`, `open Filter UniformSpace ContinuousLinearMap`, `open TracialGNS FreeWordTensor FreeBlocks`):
--
--   ```lean
--   theorem double_compression_preserves_small {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
--       (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
--       (M : VonNeumannAlgebra (boundedSubspace τ ω))
--       (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
--       (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
--       (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
--         Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
--       (hone : τ 1=1) (T : τ.GNS →L[ℂ] τ.GNS) (x : τ.GNS) :
--       doubleCompressionLeft τ ω M hconst hτ hM hone T x=doubleCompressionRight τ ω M hconst hτ hM hone T x
--   ```
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.free_position_small_corners_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Commutator/Commutator/TracialDoubleCompression.lean (declaration OAI.Kadison.TracialSequence.double_compression_preserves)

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

theorem double_compression_preserves_small {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (M : VonNeumannAlgebra (boundedSubspace τ ω))
    (hconst : ∀ a : A,leftRestricted τ ω (constantSequence a)∈M)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
      Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hone : τ 1=1) (T : τ.GNS →L[ℂ] τ.GNS) (x : τ.GNS) :
    doubleCompressionLeft τ ω M hconst hτ hM hone T x=doubleCompressionRight τ ω M hconst hτ hM hone T x := by
  sorry

end Kadison.TracialSequence

end

end OAI

end
