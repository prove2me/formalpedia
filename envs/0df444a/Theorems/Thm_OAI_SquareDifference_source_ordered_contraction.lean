-- Prove2me | Theorems.Thm_OAI_SquareDifference_source_ordered_contraction
-- name    : OAI.SquareDifference.source_ordered_contraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T12:08:50.557+00:00
-- url     : https://prove2.me/theorems/458526fe-802a-45a3-b50d-6159b8f77255
-- title:
--   OAI.SquareDifference.source_ordered_contraction: intermediate lemma from OpenAI, A power saving for square-difference-free sets
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SquareDifference.power_saving`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A power saving for square-difference-free sets*, OpenAI Math Release, September 24, 2026, result family 182, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SquareDifference.source_ordered_contraction` of [lean/OAI/Combinatorics/SquareDifference/IntervalContraction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SquareDifference/IntervalContraction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SquareDifference`, with `open Finset Filter`, `open scoped BigOperators Topology`, `open LiftTheory.SquareDifference`):
--
--   ```lean
--   lemma source_ordered_contraction {S : Type} [Fintype S] [DecidableEq S]
--       (ps : S → ℕ) [∀s,Fact (ps s).Prime] :
--       ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
--         ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
--         Function.Injective (extendedPrime ps p) → (∀j,64≤p j) →
--         (∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ)) →
--         (∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r) →
--         ∀(A : Finset ℕ),A⊆range N → NatSquareFree A →
--         ∀s : TupleVertex → ZMod (smallModulus ps),
--         (∀k<24,smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1)))) →
--         |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
--           (fun v => actualTruncatedLift p N (powerCutoff N sourceBeta)
--             (smallResidueInput (smallModulus ps) A (s v)))|≤C*(N:ℝ)^(-sourceSigma (Fintype.card TupleVertex))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SquareDifference.NatSquareFree`, `OAI.SquareDifference.TupleVertex`, `OAI.SquareDifference.actualTruncatedLift`, `OAI.SquareDifference.cycleVertex`, `OAI.SquareDifference.extendedPrime`, `OAI.SquareDifference.multilinearIntegral`, `OAI.SquareDifference.powerCutoff`, `OAI.SquareDifference.smallModulus`, `OAI.SquareDifference.smallResidueInput`, `OAI.SquareDifference.smallStrictPair`, `OAI.SquareDifference.sourceBeta`, `OAI.SquareDifference.sourceSigma`, `OAI.SquareDifference.tensorLaw`, `OAI.SquareDifference.tupleBlocks`, `OAI.SquareDifference.tupleConditionalThreshold`, `OAI.SquareDifference.tupleGoodLaw`, `OAI.SquareDifference.tupleH` and `OAI.SquareDifference.tupleMassThreshold` (definitions bundle `OAIB3Sq000` of this split).
--
--   **Used by.** The proof of `OAI.SquareDifference.power_saving` of this split imports it.
-- source:
--   OpenAI, A power saving for square-difference-free sets, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 182; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-square-difference-free-sets-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SquareDifference/IntervalContraction.lean (declaration OAI.SquareDifference.source_ordered_contraction)

import Mathlib
import Definitions.Def_OAIB3Sq000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped BigOperators Topology

namespace SquareDifference

open LiftTheory.SquareDifference

lemma source_ordered_contraction {S : Type} [Fintype S] [DecidableEq S]
    (ps : S → ℕ) [∀s,Fact (ps s).Prime] :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime],
      Function.Injective (extendedPrime ps p) → (∀j,64≤p j) →
      (∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ)) →
      (∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r) →
      ∀(A : Finset ℕ),A⊆range N → NatSquareFree A →
      ∀s : TupleVertex → ZMod (smallModulus ps),
      (∀k<24,smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1)))) →
      |multilinearIntegral (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
        (fun v => actualTruncatedLift p N (powerCutoff N sourceBeta)
          (smallResidueInput (smallModulus ps) A (s v)))|≤C*(N:ℝ)^(-sourceSigma (Fintype.card TupleVertex)) := by
  sorry

end SquareDifference

end

end OAI
end
