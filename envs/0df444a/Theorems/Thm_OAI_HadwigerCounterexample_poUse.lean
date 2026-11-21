-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_poUse
-- name    : OAI.HadwigerCounterexample.poUse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:47.538183+00:00
-- url     : https://prove2.me/theorems/263f71c1-23e3-4063-8fd6-19bd559f770a
-- title:
--   OAI.HadwigerCounterexample.poUse: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.poUse` of [lean/OAI/Combinatorics/HadwigerCounterexample/RepeatedBatchLaws.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/RepeatedBatchLaws.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample`, with `open Matrix Module LinearMap Submodule Finset Function`, `open scoped BigOperators`):
--
--   ```lean
--   theorem poUse (A B : J→NomQuery p n f) (m : Mixer p n)
--       (hN : 2*num (Full p n)<N)
--       (ha : ∀ i,Injective (pooled A i).mulVec) (hb : ∀ i, Injective (pooled B i).mulVec)
--       (F : Wgt (Rack (J×I) N)) :
--       avg (forumLaw m N) (fun x => F (peekR p (tied f J) (pooled A) (pooled B) x))=
--         avg (rackStation (database m (pooled A) (pooled B)) N) F
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.F`, `OAI.HadwigerCounterexample.Forum`, `OAI.HadwigerCounterexample.Full`, `OAI.HadwigerCounterexample.Mixer`, `OAI.HadwigerCounterexample.NomQuery`, `OAI.HadwigerCounterexample.Oframe`, `OAI.HadwigerCounterexample.PlusRack`, `OAI.HadwigerCounterexample.Port`, `OAI.HadwigerCounterexample.Rack`, `OAI.HadwigerCounterexample.Route`, `OAI.HadwigerCounterexample.Row`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.Wgt`, `OAI.HadwigerCounterexample.avg`, `OAI.HadwigerCounterexample.database`, `OAI.HadwigerCounterexample.forumLaw`, `OAI.HadwigerCounterexample.fullFintype`, `OAI.HadwigerCounterexample.num`, `OAI.HadwigerCounterexample.oframeFintype`, `OAI.HadwigerCounterexample.peekR`, `OAI.HadwigerCounterexample.pooled`, `OAI.HadwigerCounterexample.rackStation` and `OAI.HadwigerCounterexample.tied` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proofs of `OAI.HadwigerCounterexample.Template.shade_calendar` and `OAI.HadwigerCounterexample.pooled_batch` of this split import it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/RepeatedBatchLaws.lean (declaration OAI.HadwigerCounterexample.poUse)

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

attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G] [DecidableEq I]
variable [DecidableEq J] [DecidableEq G] {p : Shape} {n N : ℕ}

variable {f : Route I G}

theorem poUse (A B : J→NomQuery p n f) (m : Mixer p n)
    (hN : 2*num (Full p n)<N)
    (ha : ∀ i,Injective (pooled A i).mulVec) (hb : ∀ i, Injective (pooled B i).mulVec)
    (F : Wgt (Rack (J×I) N)) :
    avg (forumLaw m N) (fun x => F (peekR p (tied f J) (pooled A) (pooled B) x))=
      avg (rackStation (database m (pooled A) (pooled B)) N) F := by
  sorry

end HadwigerCounterexample

end

end OAI
end
