-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryEnvelopeBudgets_chosen_ofPacking_cutoff
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:16:52.738715+00:00
-- url     : https://prove2.me/theorems/422004d5-c768-4b93-ac63-b15a66cc9ef6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryEnvelopeBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryEnvelopeBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets`, with `open Filter OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic`, `open scoped Topology`):
--
--   ```lean
--   theorem chosen_ofPacking_cutoff (k C d e power ordinaryPower : ℕ) (hk : 2 ≤ k) :
--       ∃ cutoff : ℕ, ∀ n ≥ cutoff,
--         let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
--           (sparsifySchedule n) (by omega) ^ (k - 1)
--         ∀ q : Query, q.Valid → ambient q = n →
--           0 < q.clauses.length → q.clauses.length ≤ n * B →
--           q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
--           HighIncidenceProgram.Prepare.mass q.scopeRows ≤
--             (3 * n * SparseCode.degreeBound q.clauses.length B +
--               (HashSelect.loopCap n q.clauses.length + 1) *
--                 SparseCode.distanceDenom q.clauses.length B + 1) * k →
--           (∀ row ∈ q.scopeRows, row.length ≤
--             (SparseCode.degreeBound q.clauses.length B +
--               SparseCode.distanceDenom q.clauses.length B + 1) * k) →
--           ScanBounds q k (4*k+3) ∧ SmallInputs q k n ∧
--           ∀ (hg : LeafParametersProgram.Guard (q.input k))
--             (a : Word (problem q k hg).r (problem q k hg).Q)
--             (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
--             (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
--             let p := ofPacking q k B C d (2*(k-1)+1) e hg a tail
--             Bounds (2*(k-1)+1) (4*k+3) (9*e+8) n p ∧
--             (nativeEnvelope k n power ordinaryPower p : ℝ) ≤
--               (18 : ℝ)^power * (2 : ℝ)^((1 + (power : ℝ) * exponentConstant k (4*k+3)) *
--                 Statement.runtimeScale n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.degreeBound` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Resources` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.loopCap` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.exponentConstant` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.mass` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.sparsifySchedule` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Bounds` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.nativeEnvelope` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Guard` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget.chooseM` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.scopeRows` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ambient` (definitions bundle `OAIQ081S171` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ScanBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.SmallInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ofPacking` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.problem` (definitions bundle `OAIQ081S178` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeScale` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_envelope` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.trial_envelope` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryEnvelopeBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
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

theorem chosen_ofPacking_cutoff (k C d e power ordinaryPower : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      let B := 4 * DisjointReuse.SparseBudget.chooseM k 1
        (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ q : Query, q.Valid → ambient q = n →
        0 < q.clauses.length → q.clauses.length ≤ n * B →
        q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
        HighIncidenceProgram.Prepare.mass q.scopeRows ≤
          (3 * n * SparseCode.degreeBound q.clauses.length B +
            (HashSelect.loopCap n q.clauses.length + 1) *
              SparseCode.distanceDenom q.clauses.length B + 1) * k →
        (∀ row ∈ q.scopeRows, row.length ≤
          (SparseCode.degreeBound q.clauses.length B +
            SparseCode.distanceDenom q.clauses.length B + 1) * k) →
        ScanBounds q k (4*k+3) ∧ SmallInputs q k n ∧
        ∀ (hg : LeafParametersProgram.Guard (q.input k))
          (a : Word (problem q k hg).r (problem q k hg).Q)
          (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
          (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
          let p := ofPacking q k B C d (2*(k-1)+1) e hg a tail
          Bounds (2*(k-1)+1) (4*k+3) (9*e+8) n p ∧
          (nativeEnvelope k n power ordinaryPower p : ℝ) ≤
            (18 : ℝ)^power * (2 : ℝ)^((1 + (power : ℝ) * exponentConstant k (4*k+3)) *
              Statement.runtimeScale n) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets
end
