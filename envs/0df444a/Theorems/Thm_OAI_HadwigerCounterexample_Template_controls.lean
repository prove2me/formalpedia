-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_Template_controls
-- name    : OAI.HadwigerCounterexample.Template.controls
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:07:58.471953+00:00
-- url     : https://prove2.me/theorems/2807f9bc-b189-43c7-90bc-3766eaa0a742
-- title:
--   OAI.HadwigerCounterexample.Template.controls: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.Template.controls` of [lean/OAI/Combinatorics/HadwigerCounterexample/HistogramBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/HistogramBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample.Template`, with `open Finset Real Filter`, `open scoped BigOperators`):
--
--   ```lean
--   theorem controls (v : Template p I) (M : ℕ) (hM : 1≤M)
--       (Y : Type) [Fintype Y] [Nonempty Y]
--       (C η ε : ℝ) (hC : 0≤C) (hη : 0<η) (hε : 0<ε) :
--       ∃ (r : ℕ) (δ R : ℝ), 0<δ ∧ 0<R ∧ ∀ᶠ n : ℕ in atTop,
--         let N := M*n; let A := UnitType p n N
--         ∀ (m : Mixer p n), 2*num (Full p n)<N →
--         ∀ (w : Wgt A), IsLaw w →
--         (∀ i,w i ≤ bp (C*N)*pairW (raw m N) (raw m N) i) →
--         ∀ (x : I→ Wgt (Knobs p.g n)), (∀ i, IsLaw (x i)) →
--         (∀ i,mapW (x i) (freePart p)=unif) →
--         ∀ (f : A→Inputs p n I→Y),
--           let Q := fromFlags w (prodW x) f (v.resultKey)
--           Haberdash Q r δ R η ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.F`, `OAI.HadwigerCounterexample.Full`, `OAI.HadwigerCounterexample.Haberdash`, `OAI.HadwigerCounterexample.Inputs`, `OAI.HadwigerCounterexample.IsLaw`, `OAI.HadwigerCounterexample.Keys`, `OAI.HadwigerCounterexample.Knobs`, `OAI.HadwigerCounterexample.Mixer`, `OAI.HadwigerCounterexample.Orient`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.Template`, `OAI.HadwigerCounterexample.UnitType`, `OAI.HadwigerCounterexample.Vec`, `OAI.HadwigerCounterexample.Wgt`, `OAI.HadwigerCounterexample.bp`, `OAI.HadwigerCounterexample.freePart`, `OAI.HadwigerCounterexample.fromFlags`, `OAI.HadwigerCounterexample.fullFintype`, `OAI.HadwigerCounterexample.instFKeys`, `OAI.HadwigerCounterexample.knFin`, `OAI.HadwigerCounterexample.mapW`, `OAI.HadwigerCounterexample.num`, `OAI.HadwigerCounterexample.orientFintype`, `OAI.HadwigerCounterexample.pairW`, `OAI.HadwigerCounterexample.prodW`, `OAI.HadwigerCounterexample.raw`, `OAI.HadwigerCounterexample.unif`, `OAI.HadwigerCounterexample.Template.inpFinite` and `OAI.HadwigerCounterexample.Template.resultKey` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proofs of `OAI.HadwigerCounterexample.StatusAnalysis.dim_end` and `OAI.HadwigerCounterexample.StatusAnalysis.lightmap` of this split import it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/HistogramBounds.lean (declaration OAI.HadwigerCounterexample.Template.controls)

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

attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instDecidableSees _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter
open scoped BigOperators
variable {A X B C Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]

variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape}

namespace Template
set_option maxHeartbeats 1200000 in
theorem controls (v : Template p I) (M : ℕ) (hM : 1≤M)
    (Y : Type) [Fintype Y] [Nonempty Y]
    (C η ε : ℝ) (hC : 0≤C) (hη : 0<η) (hε : 0<ε) :
    ∃ (r : ℕ) (δ R : ℝ), 0<δ ∧ 0<R ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n; let A := UnitType p n N
      ∀ (m : Mixer p n), 2*num (Full p n)<N →
      ∀ (w : Wgt A), IsLaw w →
      (∀ i,w i ≤ bp (C*N)*pairW (raw m N) (raw m N) i) →
      ∀ (x : I→ Wgt (Knobs p.g n)), (∀ i, IsLaw (x i)) →
      (∀ i,mapW (x i) (freePart p)=unif) →
      ∀ (f : A→Inputs p n I→Y),
        let Q := fromFlags w (prodW x) f (v.resultKey)
        Haberdash Q r δ R η ε := by
  sorry
end Template
end HadwigerCounterexample

end

end OAI
end
