-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_NumericMarking_sample_source
-- name    : OAI.MatchingFPRAS.NumericMarking.sample_source
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:10:27.315423+00:00
-- url     : https://prove2.me/theorems/854c70bb-fc4a-4452-ae9d-f91df93d8e1b
-- title:
--   OAI.MatchingFPRAS.NumericMarking.sample_source: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.NumericMarking.sample_source` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Sampling/TreePreparedMarked.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Sampling/TreePreparedMarked.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.NumericMarking`, with `open TreeTyped TreeFraction ExecutableLadder TreeTyped.Numbered UnitRefresh NumericLadder`, `open Replica.Ladder Transport`):
--
--   ```lean
--   lemma sample_source (ft fq : List Bool) (hq : 0<fq.length)
--       (w : BagEdge bags→ℚ) (hw : ∀ e,0≤w e) (M : BagPM bags)
--       (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
--       (f : BagEdge bags→WeightedOptions (Fin 3))
--       {k n km : ℕ} (bits : Fin n→ScanBits V k) (mb : BagEdge bags→Fin km→Bool) :
--       sample (((sourcePrepared rank parent w a ft fq,Numbered.set M.val),tableRep f),
--         (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
--           (List.ofFn (orderedEnum (BagEdge bags))).map (fun e=>(index e,List.ofFn (mb e)))))=
--         numericMarks (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits
--           (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val
--             (fun e=>(f e).draw km (mb e))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.Transport.BagEdge`, `OAI.MatchingFPRAS.Transport.MatchingOn`, `OAI.MatchingFPRAS.Transport.bagEdgeFintype`, `OAI.MatchingFPRAS.Transport.bagEdgeOrder` and `OAI.MatchingFPRAS.Transport.BagEdge.Incident` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.WeightedOptions`, `OAI.MatchingFPRAS.ExecutableDP.Bags`, `OAI.MatchingFPRAS.ExecutableDP.orderedRep`, `OAI.MatchingFPRAS.ExecutableLadder.StateTable`, `OAI.MatchingFPRAS.ExecutableMarking.Marks`, `OAI.MatchingFPRAS.NumericLadder.Bits`, `OAI.MatchingFPRAS.NumericLadder.localBitsRep`, `OAI.MatchingFPRAS.NumericMarking.SampleBits`, `OAI.MatchingFPRAS.NumericMarking.numericMarks`, `OAI.MatchingFPRAS.Transport.LocalBits`, `OAI.MatchingFPRAS.Transport.ScanBits`, `OAI.MatchingFPRAS.UnitRefresh.RankedBags`, `OAI.MatchingFPRAS.UnitRefresh.numberedBags`, `OAI.MatchingFPRAS.UnitRefresh.orderedEnum`, `OAI.MatchingFPRAS.WeightedOptions.draw`, `OAI.MatchingFPRAS.Replica.Ladder.Slot`, `OAI.MatchingFPRAS.TreeTyped.Numbered.index` and `OAI.MatchingFPRAS.TreeTyped.Numbered.set` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.NumericLadder.Prepared`, `OAI.MatchingFPRAS.NumericMarking.SampleContext`, `OAI.MatchingFPRAS.NumericMarking.Tables` and `OAI.MatchingFPRAS.NumericMarking.sample` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.Transport.BagPM` and `OAI.MatchingFPRAS.Transport.ladderRun` (definitions bundle `OAIQ051M003` of this split); `OAI.MatchingFPRAS.NumericLadder.sourcePrepared` and `OAI.MatchingFPRAS.NumericMarking.tableRep` (definitions bundle `OAIQ051M004` of this split).
--
--   **Used by.** The proofs of `OAI.MatchingFPRAS.OnlineGuard.checked_mean` and `OAI.MatchingFPRAS.OnlineStage.source_mean` of this split import it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Sampling/TreePreparedMarked.lean (declaration OAI.MatchingFPRAS.NumericMarking.sample_source)

import Mathlib
import Definitions.Def_OAIQ051M004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder TreeTyped.Numbered UnitRefresh NumericLadder

open Replica.Ladder Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L} {G : SimpleGraph L}
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)
variable (rank : L→ℕ) (parent : L→Option L)
variable (hb : RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)
variable (hp : ∀ l p,parent l=some p → rank p < rank l)
lemma sample_source (ft fq : List Bool) (hq : 0<fq.length)
    (w : BagEdge bags→ℚ) (hw : ∀ e,0≤w e) (M : BagPM bags)
    (a : ExecutableDP.Bags) (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags)))
    (f : BagEdge bags→WeightedOptions (Fin 3))
    {k n km : ℕ} (bits : Fin n→ScanBits V k) (mb : BagEdge bags→Fin km→Bool) :
    sample (((sourcePrepared rank parent w a ft fq,Numbered.set M.val),tableRep f),
      (List.ofFn (fun i=>(List.ofFn (bits i).1,localBitsRep (bits i).2)),
        (List.ofFn (orderedEnum (BagEdge bags))).map (fun e=>(index e,List.ofFn (mb e)))))=
      numericMarks (ladderRun hbags hG rank parent hb hne hp hq w M k n (fun _=>M) bits
        (toLex ((0 : Fin (ft.length+1)),(⟨0,hq⟩ : Fin fq.length)))).val
          (fun e=>(f e).draw km (mb e)) := by
  sorry
end MatchingFPRAS.NumericMarking

end OAI
end
