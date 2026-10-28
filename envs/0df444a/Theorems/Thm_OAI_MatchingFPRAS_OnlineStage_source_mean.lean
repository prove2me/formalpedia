-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_OnlineStage_source_mean
-- name    : OAI.MatchingFPRAS.OnlineStage.source_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:15:27.514485+00:00
-- url     : https://prove2.me/theorems/041ae98c-e783-4499-a700-038808840210
-- title:
--   OAI.MatchingFPRAS.OnlineStage.source_mean: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.OnlineStage.source_mean` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/OnlineStage.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/OnlineStage.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.OnlineStage`, with `open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling`, `open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive`):
--
--   ```lean
--   lemma source_mean (hn : 2≤G.n) (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j)
--       (K : ℕ) (hD : 0<FiniteTrial.sourceD (G:=G) K)
--       (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
--       (ft fq : List Bool) (hq : 0<fq.length) (S k r km : ℕ)
--       (h : Fraction×Vector → ℚ) :
--       let E := BagEdge (RationalSource.bags s.activity K)
--       let keys := fun i : Fin (Fintype.card E)=>index (orderedEnum E i)
--       let req : OnlineSample.Request :=
--         (((k,Fintype.card (SourceVertex (Fin G.n) K)),r),(km,List.ofFn keys))
--       (execute (data s K (FiniteTrial.sourceD (G:=G) K) ft fq,(S,req))).mean h=
--         qaverage (fun bs : Fin S→OnlineSample.Random (Fintype.card (SourceVertex (Fin G.n) K)) k r (Fintype.card E) km=>
--           let x := fun i=>generatedSourceSample he s.activity s.activity_pos K
--             (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq (bs i).1
--             (fun e=>(bs i).2 ((orderedEnum E).symm e))
--           h (repr (s.ratioEstimate x),vectorRep (s.update hn x).scale))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.BottleneckAlgorithm.edge`, `OAI.MatchingFPRAS.Enlargement.LogicalEdge`, `OAI.MatchingFPRAS.Enlargement.SourceVertex`, `OAI.MatchingFPRAS.Enlargement.logicalEdgeLinearOrder`, `OAI.MatchingFPRAS.Enlargement.vertexLinearOrder`, `OAI.MatchingFPRAS.ExecutableScaling.Vector`, `OAI.MatchingFPRAS.Transport.BagEdge`, `OAI.MatchingFPRAS.Transport.bagEdgeFintype`, `OAI.MatchingFPRAS.Transport.bagEdgeOrder` and `OAI.MatchingFPRAS.TreeFraction.Fraction` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.FiniteTrial.ScaleState`, `OAI.MatchingFPRAS.NumberedHierarchy.NumberedComponent`, `OAI.MatchingFPRAS.NumberedHierarchy.labelOrder`, `OAI.MatchingFPRAS.NumberedHierarchy.root`, `OAI.MatchingFPRAS.OnlineSample.LocalRandom`, `OAI.MatchingFPRAS.OnlineSample.Random`, `OAI.MatchingFPRAS.OnlineSample.Request`, `OAI.MatchingFPRAS.OnlineSample.ScanRandom`, `OAI.MatchingFPRAS.PhysicalStream.Bits`, `OAI.MatchingFPRAS.PhysicalStream.qaverage`, `OAI.MatchingFPRAS.UnitRefresh.orderedEnum`, `OAI.MatchingFPRAS.FiniteTrial.ScaleState.activity`, `OAI.MatchingFPRAS.FiniteTrial.ScaleState.activity_pos`, `OAI.MatchingFPRAS.PhysicalStream.Experiment.mean` and `OAI.MatchingFPRAS.TreeTyped.Numbered.index` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.ExecutableScaling.vectorRep`, `OAI.MatchingFPRAS.ExecutableSource.SparseStageData` and `OAI.MatchingFPRAS.TreeFraction.repr` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.RationalSource.Label`, `OAI.MatchingFPRAS.RationalSource.levels` and `OAI.MatchingFPRAS.RationalSource.realB` (definitions bundle `OAIQ051M003` of this split); `OAI.MatchingFPRAS.ExecutableSource.generatedSourceSample`, `OAI.MatchingFPRAS.FiniteTrial.sourceD`, `OAI.MatchingFPRAS.OnlineStage.data`, `OAI.MatchingFPRAS.OnlineStage.execute`, `OAI.MatchingFPRAS.RationalSource.Marked`, `OAI.MatchingFPRAS.RationalSource.bags`, `OAI.MatchingFPRAS.FiniteTrial.ScaleState.ratioEstimate` and `OAI.MatchingFPRAS.FiniteTrial.ScaleState.update` (definitions bundle `OAIQ051M004` of this split); `OAI.MatchingFPRAS.GraphInput` (the published bundle `Def_MatchingFPRAS`).
--
--   **Used by.** The proofs of `OAI.MatchingFPRAS.LiteralAlgorithm.compute_mean`, `OAI.MatchingFPRAS.OnlineGuard.trial_bound` and `OAI.MatchingFPRAS.OnlineTrial.sweep_bound` of this split import it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/OnlineStage.lean (declaration OAI.MatchingFPRAS.OnlineStage.source_mean)

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStage
open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling
open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

variable {G : GraphInput} [Nontrivial (Fin G.n)]

lemma source_mean (hn : 2≤G.n) (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j)
    (K : ℕ) (hD : 0<FiniteTrial.sourceD (G:=G) K)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) (S k r km : ℕ)
    (h : Fraction×Vector → ℚ) :
    let E := BagEdge (RationalSource.bags s.activity K)
    let keys := fun i : Fin (Fintype.card E)=>index (orderedEnum E i)
    let req : OnlineSample.Request :=
      (((k,Fintype.card (SourceVertex (Fin G.n) K)),r),(km,List.ofFn keys))
    (execute (data s K (FiniteTrial.sourceD (G:=G) K) ft fq,(S,req))).mean h=
      qaverage (fun bs : Fin S→OnlineSample.Random (Fintype.card (SourceVertex (Fin G.n) K)) k r (Fintype.card E) km=>
        let x := fun i=>generatedSourceSample he s.activity s.activity_pos K
          (FiniteTrial.sourceD (G:=G) K) hD hu ft fq hq (bs i).1
          (fun e=>(bs i).2 ((orderedEnum E).symm e))
        h (repr (s.ratioEstimate x),vectorRep (s.update hn x).scale)) := by
  sorry
end MatchingFPRAS.OnlineStage

end OAI
end
