-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_law_peekR
-- name    : OAI.HadwigerCounterexample.law_peekR
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:48.111184+00:00
-- url     : https://prove2.me/theorems/7adc2771-b48d-48c3-9bcb-6cd6df33918a
-- title:
--   OAI.HadwigerCounterexample.law_peekR: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.law_peekR` of [lean/OAI/Combinatorics/HadwigerCounterexample/IndependentColumnBatches.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/IndependentColumnBatches.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample`, with `open scoped BigOperators`, `open Matrix LinearMap Module Finset Function`):
--
--   ```lean
--   theorem law_peekR (m : Mixer p n) {N : ℕ} (hN : 2*num (Full p n)<N)
--       {A B : NomQuery p n g}
--       (ha : ∀ i,Injective (A i).mulVec) (hb : ∀ i, Injective (B i).mulVec) :
--       mapW (forumLaw m N) (peekR p g A B)=rackStation (database m A B) N
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.F`, `OAI.HadwigerCounterexample.Forum`, `OAI.HadwigerCounterexample.Full`, `OAI.HadwigerCounterexample.Mixer`, `OAI.HadwigerCounterexample.NomQuery`, `OAI.HadwigerCounterexample.Oframe`, `OAI.HadwigerCounterexample.Port`, `OAI.HadwigerCounterexample.Rack`, `OAI.HadwigerCounterexample.Route`, `OAI.HadwigerCounterexample.Row`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.Wgt`, `OAI.HadwigerCounterexample.database`, `OAI.HadwigerCounterexample.forumLaw`, `OAI.HadwigerCounterexample.fullFintype`, `OAI.HadwigerCounterexample.mapW`, `OAI.HadwigerCounterexample.num`, `OAI.HadwigerCounterexample.oframeFintype`, `OAI.HadwigerCounterexample.peekR` and `OAI.HadwigerCounterexample.rackStation` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proofs of `OAI.HadwigerCounterexample.Template.controls`, `OAI.HadwigerCounterexample.Template.crane_mean`, `OAI.HadwigerCounterexample.Template.shade_calendar`, `OAI.HadwigerCounterexample.poUse` and `OAI.HadwigerCounterexample.pooled_batch` of this split import it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/IndependentColumnBatches.lean (declaration OAI.HadwigerCounterexample.law_peekR)

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAIQ430Hc000

section

attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Finset Function
variable {I G J A B : Type} [Fintype I] [Fintype G] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {p : Shape} {n N : ℕ}

variable {g : Route I G}

theorem law_peekR (m : Mixer p n) {N : ℕ} (hN : 2*num (Full p n)<N)
    {A B : NomQuery p n g}
    (ha : ∀ i,Injective (A i).mulVec) (hb : ∀ i, Injective (B i).mulVec) :
    mapW (forumLaw m N) (peekR p g A B)=rackStation (database m A B) N := by
  sorry

end HadwigerCounterexample

end

end OAI
end
