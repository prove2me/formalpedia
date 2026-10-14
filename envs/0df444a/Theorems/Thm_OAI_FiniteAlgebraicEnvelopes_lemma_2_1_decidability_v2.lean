-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_2_1_decidability_v2
-- name    : OAI.FiniteAlgebraicEnvelopes.lemma_2_1_decidability_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-12T19:41:13.756337+00:00
-- url     : https://prove2.me/theorems/9ad4468a-fe89-4405-8956-7d422998ef76
-- title:
--   Lemma 2.1, algorithmic half (the word problem survives the HNN enlargement)
-- statement:
--   With $\hat H$ the HNN extension of `lemma_2_1_construction_v2`, if $H$ has decidable word problem then so does $\hat H$.
--
--   This is the algorithmic content of the preprint's Lemma 2.1. Intuitively, a word in $\hat H$'s generators (two copies of $H$'s generators plus the stable letter $s$) is decided by repeatedly applying Britton's-Lemma pinch moves — collapsing $s(h,h)s^{-1}$ to $(1,h)$, or $s^{-1}(1,h)s$ to $(h,h)$ — whenever $H$'s own word problem decider confirms the enclosed block is diagonal (resp. in the second factor); the process terminates since each pinch strictly shortens the word, and by Britton's Lemma a word with no further pinch and at least one stable letter represents a nontrivial element. Mathlib's `HNNExtension` library proves normal forms exist via classical choice (`noncomputable`), so this decision procedure needs to be built from scratch and related back to Mathlib's theory (`HNNExtension.of_injective`, Britton's Lemma) only for its correctness proof, not for its construction.
--
--   **Formalization Note** Left open in this submission; `lemma_2_1_construction_v2` proves the non-algorithmic half of the same lemma.
-- source:
--   OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf, Lemma 2.1, p. 3.

import Mathlib
import Definitions.Def_BooneHigman
import Definitions.Def_lemma_2_1_data

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

theorem lemma_2_1_decidability_v2 {H : Type u} [Group H] [Group.FG H]
    (hH : HasDecidableWordProblem H) :
    HasDecidableWordProblem
      (HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
        (diagonalEquivSecondFactor H)) := by
  sorry

end FiniteAlgebraicEnvelopes
end OAI
