-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_StatusAnalysis_dim_end
-- name    : OAI.HadwigerCounterexample.StatusAnalysis.dim_end
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:07:15.920623+00:00
-- url     : https://prove2.me/theorems/69398033-13fc-47a6-9f57-d2760c371565
-- title:
--   OAI.HadwigerCounterexample.StatusAnalysis.dim_end: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.StatusAnalysis.dim_end` of [lean/OAI/Combinatorics/HadwigerCounterexample/IncompatibleMassBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/IncompatibleMassBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample.StatusAnalysis`, with `open Filter Finset Matrix LinearMap Function`, `open scoped BigOperators Topology`, `open Template`, `open PreparationParameters Station PredictionClass`):
--
--   ```lean
--   theorem dim_end (h:veil p M q s0 l m s w) (t:Stations p M q.pins s) (ht:∀ᶠ n in l,(t n).bank)
--       (hL:l.NeBot)
--       (b:Sketch p M) (hb:q.bright l p M m s b) (hf:q.glimmer l p M w s b) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.PreparationParameters`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.PreparationParameters.Sketch`, `OAI.HadwigerCounterexample.PreparationParameters.Stations`, `OAI.HadwigerCounterexample.PreparationParameters.bright`, `OAI.HadwigerCounterexample.PreparationParameters.cycleM`, `OAI.HadwigerCounterexample.PreparationParameters.glimmer`, `OAI.HadwigerCounterexample.PreparationParameters.pins`, `OAI.HadwigerCounterexample.PreparationParameters.rhythms`, `OAI.HadwigerCounterexample.PreparationParameters.tale`, `OAI.HadwigerCounterexample.PreparationParameters.veil` and `OAI.HadwigerCounterexample.StatusAnalysis.Station.bank` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proof of `OAI.HadwigerCounterexample.StatusAnalysis.refuteVeil` of this split imports it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/IncompatibleMassBounds.lean (declaration OAI.HadwigerCounterexample.StatusAnalysis.dim_end)

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
open PreparationParameters Station PredictionClass
variable {p : Shape} {n N K M s0 : ℕ} {q : PreparationParameters}

variable {l:Filter ℕ} {m:cycleM p} {w:tale p M} {s:rhythms p M}

set_option maxHeartbeats 1400000 in
theorem dim_end (h:veil p M q s0 l m s w) (t:Stations p M q.pins s) (ht:∀ᶠ n in l,(t n).bank)
    (hL:l.NeBot)
    (b:Sketch p M) (hb:q.bright l p M m s b) (hf:q.glimmer l p M w s b) : False := by
  sorry
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end
