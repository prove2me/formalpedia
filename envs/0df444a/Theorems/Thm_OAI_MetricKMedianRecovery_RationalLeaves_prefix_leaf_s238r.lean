-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_RationalLeaves_prefix_leaf_s238r
-- name    : OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:35:43.965215+00:00
-- url     : https://prove2.me/theorems/b38122d1-232b-4837-aeaa-f9d59124a4c2
-- title:
--   OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledLeaf.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledLeaf.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.RationalLeaves`, with `open PhaseSequence PhaseHistoryTransfer PhaseMergeInvariant PhaseMergeRefinement`):
--
--   ```lean
--   lemma prefix_leaf_s238r {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
--       {v lam eta : ℝ} {q : ℕ} {P : List (List (Label V))}
--       (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
--       (key : ℕ) (hB : Before key B) (i : V) (s : ℚ) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
--       (H : List (Label V))
--       (hH : Good (fun j=>original (loc j)) (F.image original) B (after ∅ P) v ((1+v^2)^q) lam eta H) :
--       PrefixData (fun j=>original (loc j)) (F.image original) (insert (leaf key i s) B) v lam eta (q+1)
--         (P++[H++[leaf key i s]])
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.PhaseHistoryTransfer.after` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.metric` and `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.leaf` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.PhaseMergeInvariant.PrefixData`, `OAI.MetricKMedianRecovery.PhaseMergeRefinement.Good` and `OAI.MetricKMedianRecovery.RationalLeaves.Before` (definitions bundle `Q238L020` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified_s238r` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledLeaf.lean (declaration OAI.MetricKMedianRecovery.RationalLeaves.prefix_leaf)

import Mathlib
import Definitions.Def_Q238L019
import Definitions.Def_Q238L020

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open PhaseSequence PhaseHistoryTransfer PhaseMergeInvariant PhaseMergeRefinement
variable {V : Type*} [DecidableEq V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma prefix_leaf_s238r {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v lam eta : ℝ} {q : ℕ} {P : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (key : ℕ) (hB : Before key B) (i : V) (s : ℚ) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
    (H : List (Label V))
    (hH : Good (fun j=>original (loc j)) (F.image original) B (after ∅ P) v ((1+v^2)^q) lam eta H) :
    PrefixData (fun j=>original (loc j)) (F.image original) (insert (leaf key i s) B) v lam eta (q+1)
      (P++[H++[leaf key i s]]) := by
  sorry

end MetricKMedianRecovery.RationalLeaves

end OAI
end
