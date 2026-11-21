-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_StatusAnalysis_Station_eclipse_beam
-- name    : OAI.HadwigerCounterexample.StatusAnalysis.Station.eclipse_beam
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:05:22.645041+00:00
-- url     : https://prove2.me/theorems/3fe22330-116b-4706-8f29-3917f53242f0
-- title:
--   OAI.HadwigerCounterexample.StatusAnalysis.Station.eclipse_beam: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.StatusAnalysis.Station.eclipse_beam` of [lean/OAI/Combinatorics/HadwigerCounterexample/LeafSurrogateExperiments.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/LeafSurrogateExperiments.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample.StatusAnalysis.Station`, with `open Matrix LinearMap Function Finset Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem eclipse_beam
--       (hv : ∀ i∈w.T,IsLaw (partW μ i))
--       (ha : ∀ i,IsLaw (x.qA.policies x.t x.z n i)) (hb : ∀ i,IsLaw (x.qB.policies x.t x.z n i))
--       (hN : 2*num (Messenger q × Toast p)-(N:ℝ)≤ -1) :
--       t.eclipse x m μ k Y i j - t.stagePlane x m μ k Y i j ≤
--         2*netFact (trayPort p x.t)*bp (-(N:ℝ)/2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.Canopy`, `OAI.HadwigerCounterexample.Comp`, `OAI.HadwigerCounterexample.IsLaw`, `OAI.HadwigerCounterexample.Knobs`, `OAI.HadwigerCounterexample.LeafMixture`, `OAI.HadwigerCounterexample.Mixer`, `OAI.HadwigerCounterexample.Orient`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.Silhouette`, `OAI.HadwigerCounterexample.Tag`, `OAI.HadwigerCounterexample.Toast`, `OAI.HadwigerCounterexample.UnitType`, `OAI.HadwigerCounterexample.Wgt`, `OAI.HadwigerCounterexample.bp`, `OAI.HadwigerCounterexample.knFin`, `OAI.HadwigerCounterexample.netFact`, `OAI.HadwigerCounterexample.num`, `OAI.HadwigerCounterexample.orientFintype`, `OAI.HadwigerCounterexample.partW`, `OAI.HadwigerCounterexample.trayPort`, `OAI.HadwigerCounterexample.StatusAnalysis.Format`, `OAI.HadwigerCounterexample.StatusAnalysis.Grid`, `OAI.HadwigerCounterexample.StatusAnalysis.Messenger`, `OAI.HadwigerCounterexample.StatusAnalysis.Nodes`, `OAI.HadwigerCounterexample.StatusAnalysis.Rates`, `OAI.HadwigerCounterexample.StatusAnalysis.Station`, `OAI.HadwigerCounterexample.StatusAnalysis.Typus`, `OAI.HadwigerCounterexample.StatusAnalysis.deckMax`, `OAI.HadwigerCounterexample.StatusAnalysis.Quill.policies`, `OAI.HadwigerCounterexample.StatusAnalysis.Station.eclipse` and `OAI.HadwigerCounterexample.StatusAnalysis.Station.stagePlane` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proof of `OAI.HadwigerCounterexample.StatusAnalysis.lightmap` of this split imports it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/LeafSurrogateExperiments.lean (declaration OAI.HadwigerCounterexample.StatusAnalysis.Station.eclipse_beam)

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
open Matrix LinearMap Function Finset Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K s M : ℕ}
  {w : LeafMixture p n N} {q : Format} {d e : Rates}

namespace Station
variable (t : Station p n N K w) (x : Typus p q d e)
  (m : Mixer p n) (μ : Wgt (UnitType p n N)) (k : Fin (2^deckMax p K))
variable (Y : Silhouette p N s) (i j : w.T)

set_option maxHeartbeats 900000 in
theorem eclipse_beam
    (hv : ∀ i∈w.T,IsLaw (partW μ i))
    (ha : ∀ i,IsLaw (x.qA.policies x.t x.z n i)) (hb : ∀ i,IsLaw (x.qB.policies x.t x.z n i))
    (hN : 2*num (Messenger q × Toast p)-(N:ℝ)≤ -1) :
    t.eclipse x m μ k Y i j - t.stagePlane x m μ k Y i j ≤
      2*netFact (trayPort p x.t)*bp (-(N:ℝ)/2) := by
  sorry

end Station

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end
