-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_RationalLeaves_zero_free_replay_s238r
-- name    : OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:35:40.935188+00:00
-- url     : https://prove2.me/theorems/0d8f81e4-9fc0-41d5-a8a3-6d06b61d802f
-- title:
--   OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/LeafReplay.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/LeafReplay.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.RationalLeaves`, with `open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing`):
--
--   ```lean
--   lemma zero_free_replay_s238r (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
--       (key : ℕ) (i : V) (f : Label V) (H : List (Label V)) (T : List (List (Label V)))
--       (v lam eta : ℝ) (q n : ℕ) (hB : Before key B) (hdis : Disjoint (F.image original) B)
--       (hQ : Q⊆F.image original ∪ B) (hf : f∈B) (hd : ∀ j,dist (original (loc j)) (original i)=dist (original (loc j)) f)
--       (ht : 0≤1-3*v) (hlam : 0<lam)
--       (hphase : Valid (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta (H++[f]))
--       (h : Runs (fun j=>original (loc j)) (F.image original) B (Q∪(H++[f]).toFinset) v lam (q+1) n T) :
--       Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i 0) B)
--         (insert (leaf key i 0) (Q∪H.toFinset)) v lam (q+1) n T ∧
--         finalCount (F.image original) Q (H++[f]) T =
--           ((after (insert (leaf key i 0) (Q∪H.toFinset)) T)∩F.image original).card
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.finalCount` and `OAI.MetricKMedianRecovery.PhaseHistoryTransfer.after` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.metric` and `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.leaf` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Runs`, `OAI.MetricKMedianRecovery.PhaseSequence.Valid` and `OAI.MetricKMedianRecovery.RationalLeaves.Before` (definitions bundle `Q238L020` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/LeafReplay.lean (declaration OAI.MetricKMedianRecovery.RationalLeaves.zero_free_replay)

import Mathlib
import Definitions.Def_Q238L019
import Definitions.Def_Q238L020

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] metric

lemma zero_free_replay_s238r (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (key : ℕ) (i : V) (f : Label V) (H : List (Label V)) (T : List (List (Label V)))
    (v lam eta : ℝ) (q n : ℕ) (hB : Before key B) (hdis : Disjoint (F.image original) B)
    (hQ : Q⊆F.image original ∪ B) (hf : f∈B) (hd : ∀ j,dist (original (loc j)) (original i)=dist (original (loc j)) f)
    (ht : 0≤1-3*v) (hlam : 0<lam)
    (hphase : Valid (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta (H++[f]))
    (h : Runs (fun j=>original (loc j)) (F.image original) B (Q∪(H++[f]).toFinset) v lam (q+1) n T) :
    Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i 0) B)
      (insert (leaf key i 0) (Q∪H.toFinset)) v lam (q+1) n T ∧
      finalCount (F.image original) Q (H++[f]) T =
        ((after (insert (leaf key i 0) (Q∪H.toFinset)) T)∩F.image original).card := by
  sorry

end MetricKMedianRecovery.RationalLeaves

end OAI
end
