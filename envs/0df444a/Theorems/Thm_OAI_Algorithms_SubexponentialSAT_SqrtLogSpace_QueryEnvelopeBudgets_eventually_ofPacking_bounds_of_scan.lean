-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryEnvelopeBudgets_eventually_ofPacking_bounds_of_scan
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:17:29.369356+00:00
-- url     : https://prove2.me/theorems/164413bf-4acd-47ce-8a8a-6af78501377d
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryEnvelopeBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryEnvelopeBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets`, with `open Filter OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic`, `open scoped Topology`):
--
--   ```lean
--   theorem eventually_ofPacking_bounds_of_scan (k qi ql C d e : ℕ) :
--       ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), ambient q = n →
--         ScanBounds q k ql → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
--         ∀ (hg : LeafParametersProgram.Guard (q.input k))
--           (a : Word (problem q k hg).r (problem q k hg).Q)
--           (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
--           (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
--           Bounds qi ql (9*e+8) n (ofPacking q k B C d qi e hg a tail)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Bounds` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ScanBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ofPacking` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.problem` (definitions bundle `OAIQ081S178` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryEnvelopeBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets

open Filter OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic
  OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources
  OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open scoped Topology

noncomputable section

theorem eventually_ofPacking_bounds_of_scan (k qi ql C d e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), ambient q = n →
      ScanBounds q k ql → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      ∀ (hg : LeafParametersProgram.Guard (q.input k))
        (a : Word (problem q k hg).r (problem q k hg).Q)
        (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
        (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
        Bounds qi ql (9*e+8) n (ofPacking q k B C d qi e hg a tail) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets
end
