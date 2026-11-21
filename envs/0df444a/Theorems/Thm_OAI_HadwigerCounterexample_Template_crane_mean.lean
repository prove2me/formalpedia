-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_Template_crane_mean
-- name    : OAI.HadwigerCounterexample.Template.crane_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:33.012049+00:00
-- url     : https://prove2.me/theorems/ab9d7510-53b9-4258-8d92-ddc93d958446
-- title:
--   OAI.HadwigerCounterexample.Template.crane_mean: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.Template.crane_mean` of [lean/OAI/Combinatorics/HadwigerCounterexample/FourCornerTrials.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/FourCornerTrials.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample.Template`, with `open Finset Matrix Module LinearMap Function`, `open scoped BigOperators`):
--
--   ```lean
--   theorem crane_mean (v : Template p I) (j : I) (q : I → F) (U : Wgt (Keys (p:=p) v.t N))
--       (T : Wgt (Inputs p n I)) (w : I→ Wgt (Knobs p.g n))
--       (hw : ∀ i,IsLaw (w i)) (hz : ∀ i,mapW (w i) (freePart p)=unif)
--       (m : Mixer p n) (hN : 2*num (Full p n)<N)
--       (δ : ℝ) (hδ : 0≤δ) (hU : ∀ i,|U i|≤1) (hT : ∀ i,|T i|≤1)
--       (h : chairCut v j U δ) (hW : carried U (ownPart (p:=p) v.t q))
--       (k : ℝ) (hk : ∀ i,num (Port v.seam i)≤ k) (hK : 2*k - (N:ℝ) ≤ -1) :
--       let μ := raw m N; let W := netFact v.seam
--       |avg (pairW μ μ) (v.crane j T U w)| ≤ 2*W * (num (Ports p)*(2*bp (k-N)))+
--         W*(δ+bp (-(N:ℝ)/2)) + bp (num Bool*num I-n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.Comp`, `OAI.HadwigerCounterexample.F`, `OAI.HadwigerCounterexample.Full`, `OAI.HadwigerCounterexample.Inputs`, `OAI.HadwigerCounterexample.IsLaw`, `OAI.HadwigerCounterexample.KeySlots`, `OAI.HadwigerCounterexample.Keys`, `OAI.HadwigerCounterexample.Knobs`, `OAI.HadwigerCounterexample.Mixer`, `OAI.HadwigerCounterexample.Orient`, `OAI.HadwigerCounterexample.Port`, `OAI.HadwigerCounterexample.Ports`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.Tag`, `OAI.HadwigerCounterexample.Template`, `OAI.HadwigerCounterexample.Vec`, `OAI.HadwigerCounterexample.Wgt`, `OAI.HadwigerCounterexample.avg`, `OAI.HadwigerCounterexample.bp`, `OAI.HadwigerCounterexample.carried`, `OAI.HadwigerCounterexample.freePart`, `OAI.HadwigerCounterexample.fullFintype`, `OAI.HadwigerCounterexample.knFin`, `OAI.HadwigerCounterexample.mapW`, `OAI.HadwigerCounterexample.netFact`, `OAI.HadwigerCounterexample.num`, `OAI.HadwigerCounterexample.orientFintype`, `OAI.HadwigerCounterexample.ownPart`, `OAI.HadwigerCounterexample.pairW`, `OAI.HadwigerCounterexample.raw`, `OAI.HadwigerCounterexample.unif`, `OAI.HadwigerCounterexample.Template.PackSlot`, `OAI.HadwigerCounterexample.Template.chairCut`, `OAI.HadwigerCounterexample.Template.crane`, `OAI.HadwigerCounterexample.Template.keySlotFinite` and `OAI.HadwigerCounterexample.Template.seam` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proof of `OAI.HadwigerCounterexample.Template.shade_calendar` of this split imports it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/FourCornerTrials.lean (declaration OAI.HadwigerCounterexample.Template.crane_mean)

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAIQ430Hc000

section

attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

set_option maxHeartbeats 1000000 in
theorem crane_mean (v : Template p I) (j : I) (q : I → F) (U : Wgt (Keys (p:=p) v.t N))
    (T : Wgt (Inputs p n I)) (w : I→ Wgt (Knobs p.g n))
    (hw : ∀ i,IsLaw (w i)) (hz : ∀ i,mapW (w i) (freePart p)=unif)
    (m : Mixer p n) (hN : 2*num (Full p n)<N)
    (δ : ℝ) (hδ : 0≤δ) (hU : ∀ i,|U i|≤1) (hT : ∀ i,|T i|≤1)
    (h : chairCut v j U δ) (hW : carried U (ownPart (p:=p) v.t q))
    (k : ℝ) (hk : ∀ i,num (Port v.seam i)≤ k) (hK : 2*k - (N:ℝ) ≤ -1) :
    let μ := raw m N; let W := netFact v.seam
    |avg (pairW μ μ) (v.crane j T U w)| ≤ 2*W * (num (Ports p)*(2*bp (k-N)))+
      W*(δ+bp (-(N:ℝ)/2)) + bp (num Bool*num I-n) := by
  sorry
end Template
end HadwigerCounterexample

end

end OAI
end
