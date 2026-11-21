-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_StatusAnalysis_Quill_sideRelease
-- name    : OAI.HadwigerCounterexample.StatusAnalysis.Quill.sideRelease
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:05:40.022832+00:00
-- url     : https://prove2.me/theorems/62d3a515-5e37-4c2a-8cbb-27692cb627b2
-- title:
--   OAI.HadwigerCounterexample.StatusAnalysis.Quill.sideRelease: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.StatusAnalysis.Quill.sideRelease` of [lean/OAI/Combinatorics/HadwigerCounterexample/UniformSideComparisons.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/UniformSideComparisons.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample.StatusAnalysis.Quill`, with `open Filter Finset Matrix Function`, `open scoped BigOperators Topology`, `open Template`):
--
--   ```lean
--   theorem sideRelease (M:ℕ) (h : AnalyticParameters p M b' s0) (hw : w.moral t z) (ε:ℝ) (he:0<ε) :
--       ∃ (l:ℕ) (u c:ℝ),0<u∧0 < c∧∀ᶠ n : ℕ in atTop,let N:=M*n;∀ W:Wgt (Keys (p:=p) t N),
--         (∀ x, |W x|≤ 1) → ∃ X: Silhouette p N l,w.markedTest t z M b' s0 n X W (bp (-c*n)) u ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.AnalyticParameters`, `OAI.HadwigerCounterexample.F`, `OAI.HadwigerCounterexample.Keys`, `OAI.HadwigerCounterexample.PreparationParameters`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.Silhouette`, `OAI.HadwigerCounterexample.Tagging`, `OAI.HadwigerCounterexample.Wgt`, `OAI.HadwigerCounterexample.bp`, `OAI.HadwigerCounterexample.StatusAnalysis.Format`, `OAI.HadwigerCounterexample.StatusAnalysis.Messenger`, `OAI.HadwigerCounterexample.StatusAnalysis.Quill`, `OAI.HadwigerCounterexample.StatusAnalysis.Rates`, `OAI.HadwigerCounterexample.StatusAnalysis.Quill.markedTest` and `OAI.HadwigerCounterexample.StatusAnalysis.Quill.moral` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proofs of `OAI.HadwigerCounterexample.StatusAnalysis.Quill.soberCalendar` and `OAI.HadwigerCounterexample.StatusAnalysis.lightmap` of this split import it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/UniformSideComparisons.lean (declaration OAI.HadwigerCounterexample.StatusAnalysis.Quill.sideRelease)

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAIQ430Hc000

section

attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N r s0 : ℕ}
namespace StatusAnalysis
namespace Quill
variable {q : Format} {d : Rates} {b:Bool}
    (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
variable {b' : PreparationParameters}

set_option maxHeartbeats 1600000 in
theorem sideRelease (M:ℕ) (h : AnalyticParameters p M b' s0) (hw : w.moral t z) (ε:ℝ) (he:0<ε) :
    ∃ (l:ℕ) (u c:ℝ),0<u∧0 < c∧∀ᶠ n : ℕ in atTop,let N:=M*n;∀ W:Wgt (Keys (p:=p) t N),
      (∀ x, |W x|≤ 1) → ∃ X: Silhouette p N l,w.markedTest t z M b' s0 n X W (bp (-c*n)) u ε := by
  sorry

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end
