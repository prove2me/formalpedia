-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_leaf_certified_s238r
-- name    : OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:38:53.419702+00:00
-- url     : https://prove2.me/theorems/3a74f7c3-2afb-4728-9c18-7d1259d2e586
-- title:
--   OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledLeaf.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledLeaf.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalCoupledMerge`, with `open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing`):
--
--   ```lean
--   lemma leaf_certified_s238r {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
--       {v eta lo hi : ℝ} {lam : ℚ} {q n k : ℕ} {P : List (List (Label V))}
--       (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
--       (key : ℕ) (hB : Before key B) (hkey : key<3*(q+1))
--       (i : V) (H : List (Label V)) (l u : ℚ) (T U : List (List (Label V)))
--       (hv : 0<v) (hv1 : v<1/6) (hlam : (0:ℝ)<lam) (hd : Disjoint (F.image original) B)
--       (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
--       (hH : Good (fun j=>original (loc j)) (F.image original) B (after ∅ P) v ((1+v^2)^q) lam eta H)
--       (hl0 : 0≤l) (hlu : l≤u) (hw : (u:ℝ)-(l:ℝ)≤eta)
--       (hT : Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i l) B)
--         (insert (leaf key i l) (after ∅ P∪H.toFinset)) v lam (q+1) n T)
--       (hU : Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i u) B)
--         (insert (leaf key i u) (after ∅ P∪H.toFinset)) v lam (q+1) n U)
--       (hs : Sandwich k ((after (insert (leaf key i l) (after ∅ P∪H.toFinset)) T)∩F.image original).card
--         ((after (insert (leaf key i u) (after ∅ P∪H.toFinset)) U)∩F.image original).card) :
--       Certified loc F v eta lo hi (q+1) n k (leafState B P lam key i H l u T U)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.PhaseCountCrossing.Sandwich` and `OAI.MetricKMedianRecovery.PhaseHistoryTransfer.after` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.metric` and `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.leaf` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Runs`, `OAI.MetricKMedianRecovery.PhaseMergeInvariant.PrefixData`, `OAI.MetricKMedianRecovery.PhaseMergeRefinement.Good` and `OAI.MetricKMedianRecovery.RationalLeaves.Before` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Certified` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leafState` (definitions bundle `Q238L026` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledLeaf.lean (declaration OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified)

import Mathlib
import Definitions.Def_Q238L026

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

lemma leaf_certified_s238r {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v eta lo hi : ℝ} {lam : ℚ} {q n k : ℕ} {P : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (key : ℕ) (hB : Before key B) (hkey : key<3*(q+1))
    (i : V) (H : List (Label V)) (l u : ℚ) (T U : List (List (Label V)))
    (hv : 0<v) (hv1 : v<1/6) (hlam : (0:ℝ)<lam) (hd : Disjoint (F.image original) B)
    (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hH : Good (fun j=>original (loc j)) (F.image original) B (after ∅ P) v ((1+v^2)^q) lam eta H)
    (hl0 : 0≤l) (hlu : l≤u) (hw : (u:ℝ)-(l:ℝ)≤eta)
    (hT : Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i l) B)
      (insert (leaf key i l) (after ∅ P∪H.toFinset)) v lam (q+1) n T)
    (hU : Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i u) B)
      (insert (leaf key i u) (after ∅ P∪H.toFinset)) v lam (q+1) n U)
    (hs : Sandwich k ((after (insert (leaf key i l) (after ∅ P∪H.toFinset)) T)∩F.image original).card
      ((after (insert (leaf key i u) (after ∅ P∪H.toFinset)) U)∩F.image original).card) :
    Certified loc F v eta lo hi (q+1) n k (leafState B P lam key i H l u T U) := by
  sorry

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end
