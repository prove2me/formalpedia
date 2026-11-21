-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_PreparationParameters_veil_score_cost
-- name    : OAI.HadwigerCounterexample.PreparationParameters.veil.score_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:05:40.40374+00:00
-- url     : https://prove2.me/theorems/13d167ab-1a8a-4f8e-a898-7fb191f7808b
-- title:
--   OAI.HadwigerCounterexample.PreparationParameters.veil.score_cost: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.PreparationParameters.veil.score_cost` of [lean/OAI/Combinatorics/HadwigerCounterexample/AnalyticParameters.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/AnalyticParameters.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample.PreparationParameters`, with `open Filter Finset Matrix`, `open scoped BigOperators Topology`, `open StatusAnalysis StatusAnalysis.Station`):
--
--   ```lean
--   theorem veil.score_cost (h : veil p M b r l m s w)
--       (v : Stations p M b.pins s) :
--       ∃ δ : ℕ → ℝ,ExpSmall l (fun n=> ((M*n:ℕ):ℝ)) δ ∧
--         ∀ᶠ n in l, ∀ (q : Format) (d e : Rates) (x : Typus p q d e) (k : Fin (2^deckMax p b.pins)),
--           |arena (v n) x (m n) (w n) k|≤δ n
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.ExpSmall`, `OAI.HadwigerCounterexample.PreparationParameters`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.PreparationParameters.Stations`, `OAI.HadwigerCounterexample.PreparationParameters.cycleM`, `OAI.HadwigerCounterexample.PreparationParameters.pins`, `OAI.HadwigerCounterexample.PreparationParameters.rhythms`, `OAI.HadwigerCounterexample.PreparationParameters.tale`, `OAI.HadwigerCounterexample.PreparationParameters.veil`, `OAI.HadwigerCounterexample.StatusAnalysis.Format`, `OAI.HadwigerCounterexample.StatusAnalysis.Rates`, `OAI.HadwigerCounterexample.StatusAnalysis.Typus`, `OAI.HadwigerCounterexample.StatusAnalysis.deckMax` and `OAI.HadwigerCounterexample.StatusAnalysis.Station.arena` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proofs of `OAI.HadwigerCounterexample.StatusAnalysis.dim_end` and `OAI.HadwigerCounterexample.StatusAnalysis.lightmap` of this split import it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/AnalyticParameters.lean (declaration OAI.HadwigerCounterexample.PreparationParameters.veil.score_cost)

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

attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open StatusAnalysis StatusAnalysis.Station

namespace PreparationParameters
variable {b : PreparationParameters} {p : Shape} {N M r : ℕ} {l : Filter ℕ} {m : cycleM p}
  {s : rhythms p M} {w : tale p M}

set_option maxHeartbeats 1200000 in
theorem veil.score_cost (h : veil p M b r l m s w)
    (v : Stations p M b.pins s) :
    ∃ δ : ℕ → ℝ,ExpSmall l (fun n=> ((M*n:ℕ):ℝ)) δ ∧
      ∀ᶠ n in l, ∀ (q : Format) (d e : Rates) (x : Typus p q d e) (k : Fin (2^deckMax p b.pins)),
        |arena (v n) x (m n) (w n) k|≤δ n := by
  sorry

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end
