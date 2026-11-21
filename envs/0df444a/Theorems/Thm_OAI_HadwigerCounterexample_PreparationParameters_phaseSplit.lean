-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_PreparationParameters_phaseSplit
-- name    : OAI.HadwigerCounterexample.PreparationParameters.phaseSplit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:05:41.683649+00:00
-- url     : https://prove2.me/theorems/a2281bde-a73d-4da2-b1a1-6dd1ee9bd0c4
-- title:
--   OAI.HadwigerCounterexample.PreparationParameters.phaseSplit: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.PreparationParameters.phaseSplit` of [lean/OAI/Combinatorics/HadwigerCounterexample/PreliminaryRestrictions.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/PreliminaryRestrictions.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample.PreparationParameters`, with `open Filter Finset Matrix`, `open scoped BigOperators Topology`, `open PredictionClass`):
--
--   ```lean
--   theorem phaseSplit (hl : l≤atTop) (hq : q.planted p M)
--       (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
--       (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
--       (hb : q.dosed l p M m w s b P)
--       (he : ∀ᶠ n in l, (s n).within
--         (fun x=> P n x → delta (b.m n) x ≠ 0)) :
--       ∃ R : Campaign p M, q.citable l p M m w s b R ∧ ∀ᶠ n in l,
--         let v:=potion s w R n
--         tonalMix p (delta (b.m n)) v ∨ tonalTiny p (delta (b.m n)) v q.d
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.Ambient`, `OAI.HadwigerCounterexample.Comp`, `OAI.HadwigerCounterexample.F`, `OAI.HadwigerCounterexample.Mat`, `OAI.HadwigerCounterexample.PreparationParameters`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.UnitType`, `OAI.HadwigerCounterexample.Wgt`, `OAI.HadwigerCounterexample.delta`, `OAI.HadwigerCounterexample.tonalMix`, `OAI.HadwigerCounterexample.tonalTiny`, `OAI.HadwigerCounterexample.LeafMixture.X`, `OAI.HadwigerCounterexample.LeafMixture.within`, `OAI.HadwigerCounterexample.PreparationParameters.Campaign`, `OAI.HadwigerCounterexample.PreparationParameters.Sketch`, `OAI.HadwigerCounterexample.PreparationParameters.citable`, `OAI.HadwigerCounterexample.PreparationParameters.cycleM`, `OAI.HadwigerCounterexample.PreparationParameters.dosed`, `OAI.HadwigerCounterexample.PreparationParameters.entered`, `OAI.HadwigerCounterexample.PreparationParameters.nascent`, `OAI.HadwigerCounterexample.PreparationParameters.planted`, `OAI.HadwigerCounterexample.PreparationParameters.potion`, `OAI.HadwigerCounterexample.PreparationParameters.rhythms` and `OAI.HadwigerCounterexample.PreparationParameters.tale` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proof of `OAI.HadwigerCounterexample.eventual_conflict_lower_bound` of this split imports it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/PreliminaryRestrictions.lean (declaration OAI.HadwigerCounterexample.PreparationParameters.phaseSplit)

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

attribute [-instance] _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open PredictionClass
namespace PreparationParameters

variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : rhythms p M} {w : tale p M} {b : Sketch p M} {P : Campaign p M}

set_option maxHeartbeats 900000 in
theorem phaseSplit (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.dosed l p M m w s b P)
    (he : ∀ᶠ n in l, (s n).within
      (fun x=> P n x → delta (b.m n) x ≠ 0)) :
    ∃ R : Campaign p M, q.citable l p M m w s b R ∧ ∀ᶠ n in l,
      let v:=potion s w R n
      tonalMix p (delta (b.m n)) v ∨ tonalTiny p (delta (b.m n)) v q.d := by
  sorry

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end
