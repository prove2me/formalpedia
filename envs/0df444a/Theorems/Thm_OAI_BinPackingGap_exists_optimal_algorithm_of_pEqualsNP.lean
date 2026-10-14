-- Prove2me | Theorems.Thm_OAI_BinPackingGap_exists_optimal_algorithm_of_pEqualsNP
-- name    : OAI.BinPackingGap.exists_optimal_algorithm_of_pEqualsNP
-- status  : Open
-- author  : @SamenHossain
-- created : 2026-10-12T18:06:49.839702+00:00
-- url     : https://prove2.me/theorems/8135c2d4-9b2a-4cba-b426-cea48914856a
-- title:
--   If P = NP, bin packing has an exact polynomial-time algorithm on binary encodings
-- statement:
--   Assume $\mathrm P=\mathrm{NP}$ (`PEqualsNP`). Then there is an **absolute additive algorithm with error $0$**: a finite-alphabet, polynomial-time Turing machine on binary strings with the following behaviour.
--   1. On the encoding of every valid raw instance (a list of rational sizes in $(0,1]$), it outputs a feasible packing whose number of bins equals the optimum $\mathrm{OPT}$.
--   2. On the encoding of the empty instance, it outputs the empty packing $\langle 0,[\,]\rangle$.
--   3. On every input that does not decode to a raw instance, it outputs `none`.
--   4. On the encoding of every invalid raw instance, it outputs `none`.
--
--   This is the fourth clause of `OAI.BinPackingGap.main_results`. It also gives the backward direction of the third clause, with $c=0$.
-- source:
--   OpenAI, *Additive hardness and unbounded configuration gaps in bin packing*, preprint, September 24, 2026 (https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf). Formal statement: openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/BinPacking/Results/OptimalSearch.lean, definition `absoluteAdditiveAlgorithm_of_pEqualsNP` with the theorems `absoluteAdditiveAlgorithm_of_pEqualsNP_optimal`, `_empty`, `_malformed` and `_invalid`, combined exactly as in the fourth conjunct of `main_results` in https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BinPackingGap.lean.

import Mathlib
import Definitions.Def_BinPackingGap

namespace OAI

noncomputable section

namespace BinPackingGap

open scoped BigOperators

theorem exists_optimal_algorithm_of_pEqualsNP :
    PEqualsNP → ∃ algorithm : AbsoluteAdditiveAlgorithm 0,
    (∀ (items : RawInstance) (valid : items.Valid), ∃ packing : RawPacking,
      algorithm.run (BinaryEncoding.rawInstanceBits items) = some packing ∧
      packing.Feasible items ∧ packing.bins = opt (items.toInstance valid)) ∧
    algorithm.run (BinaryEncoding.rawInstanceBits []) = some ⟨0, []⟩ ∧
    (∀ input : List Bool, BinaryEncoding.decodeRawInstance input = none →
      algorithm.run input = none) ∧
    (∀ items : RawInstance, ¬ items.Valid →
      algorithm.run (BinaryEncoding.rawInstanceBits items) = none) := by
  sorry

end BinPackingGap
end
end OAI
