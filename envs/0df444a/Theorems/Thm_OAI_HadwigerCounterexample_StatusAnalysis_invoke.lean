-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_StatusAnalysis_invoke
-- name    : OAI.HadwigerCounterexample.StatusAnalysis.invoke
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:05:58.697183+00:00
-- url     : https://prove2.me/theorems/d7edcc80-13dc-4873-bc7a-babc58185057
-- title:
--   OAI.HadwigerCounterexample.StatusAnalysis.invoke: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.StatusAnalysis.invoke` of [lean/OAI/Combinatorics/HadwigerCounterexample/CompatibleTableEvents.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/CompatibleTableEvents.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample.StatusAnalysis`, with `open Filter Finset Matrix LinearMap Function`, `open scoped BigOperators Topology`, `open Template`, `open PreparationParameters PredictionClass`):
--
--   ```lean
--   theorem invoke (k:Fin (2^deckMax p q.pins))
--       (r:F) (a:ℝ) (hα:0<a) (h:AnalyticParameters p M q s0)
--       (hw:Settled w m q U z r) (ht:v.bank)
--       (hk:2*a ≤ pr (pairW (partW U i.val) (partW U j.val))
--          (fun x=> shimmer z r x∧ berthTicket (w.pin i.val) (w.pin j.val) (v.mails i j k) x)) :
--       ∃ x:Scrip p q.pins, v.charter x.2.2 m x.2.1 U a (i,j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.AnalyticParameters`, `OAI.HadwigerCounterexample.BMark`, `OAI.HadwigerCounterexample.Canopy`, `OAI.HadwigerCounterexample.F`, `OAI.HadwigerCounterexample.LeafMixture`, `OAI.HadwigerCounterexample.Mixer`, `OAI.HadwigerCounterexample.Orient`, `OAI.HadwigerCounterexample.PreparationParameters`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.UnitType`, `OAI.HadwigerCounterexample.Wgt`, `OAI.HadwigerCounterexample.orientFintype`, `OAI.HadwigerCounterexample.pairW`, `OAI.HadwigerCounterexample.partW`, `OAI.HadwigerCounterexample.pr`, `OAI.HadwigerCounterexample.PreparationParameters.pins`, `OAI.HadwigerCounterexample.StatusAnalysis.Master`, `OAI.HadwigerCounterexample.StatusAnalysis.OnFile`, `OAI.HadwigerCounterexample.StatusAnalysis.Scrip`, `OAI.HadwigerCounterexample.StatusAnalysis.Settled`, `OAI.HadwigerCounterexample.StatusAnalysis.Stakes`, `OAI.HadwigerCounterexample.StatusAnalysis.Station`, `OAI.HadwigerCounterexample.StatusAnalysis.Volumes`, `OAI.HadwigerCounterexample.StatusAnalysis.berthTicket`, `OAI.HadwigerCounterexample.StatusAnalysis.deckMax`, `OAI.HadwigerCounterexample.StatusAnalysis.shimmer`, `OAI.HadwigerCounterexample.StatusAnalysis.toFormat`, `OAI.HadwigerCounterexample.StatusAnalysis.toRates`, `OAI.HadwigerCounterexample.StatusAnalysis.Station.bank` and `OAI.HadwigerCounterexample.StatusAnalysis.Station.charter` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proof of `OAI.HadwigerCounterexample.StatusAnalysis.dim_end` of this split imports it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/CompatibleTableEvents.lean (declaration OAI.HadwigerCounterexample.StatusAnalysis.invoke)

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
open Filter Finset Matrix LinearMap Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters PredictionClass

variable {p:Shape} {n M K s0 N :ℕ} {w:LeafMixture p n N} {q:PreparationParameters}

variable (v: Station p n N q.pins w) (i j:w.T)
    (U:Wgt (UnitType p n N)) (m:Mixer p n) (z:BMark p n N)

set_option maxHeartbeats 1800000 in
theorem invoke (k:Fin (2^deckMax p q.pins))
    (r:F) (a:ℝ) (hα:0<a) (h:AnalyticParameters p M q s0)
    (hw:Settled w m q U z r) (ht:v.bank)
    (hk:2*a ≤ pr (pairW (partW U i.val) (partW U j.val))
       (fun x=> shimmer z r x∧ berthTicket (w.pin i.val) (w.pin j.val) (v.mails i j k) x)) :
    ∃ x:Scrip p q.pins, v.charter x.2.2 m x.2.1 U a (i,j) := by
  sorry

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end
