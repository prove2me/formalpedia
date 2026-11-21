-- Prove2me | Theorems.Thm_OAI_HadwigerCounterexample_Template_shade_calendar
-- name    : OAI.HadwigerCounterexample.Template.shade_calendar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-20T23:06:30.828956+00:00
-- url     : https://prove2.me/theorems/886c6ed4-0927-4dba-8f7c-ef7bec0ba7ae
-- title:
--   OAI.HadwigerCounterexample.Template.shade_calendar: intermediate lemma from OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HadwigerCounterexample.Template.shade_calendar` of [lean/OAI/Combinatorics/HadwigerCounterexample/CutIntegralBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/CutIntegralBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HadwigerCounterexample.Template`, with `open Finset Real Matrix Function Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem shade_calendar (v : Template p I) (j : I) (M : ℕ) (hM : 1≤M)
--       (C ε : ℝ) (hε : 0<ε) :
--       ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
--         let N := M*n
--         ∀ (q : I→F) (U : Wgt (Keys (p:=p) v.t N)) (T : Wgt (Inputs p n I))
--           (w : I→Wgt (Knobs p.g n)), (∀ x, |U x|≤1) → chairCut v j U δ →
--           carried U (ownPart (p:=p) v.t q) →
--           (∀ x, |T x|≤1) → (∀ i,IsLaw (w i)) →
--           (∀ i,mapW (w i) (freePart p)=unif) →
--         ∀ (m : Mixer p n), 2*num (Full p n)<N →
--         let μ:=raw m N; let H:=bp ((1/32:ℝ)*n)
--         ∀ (ρ : Wgt (UnitType p n N)), IsLaw ρ →
--         (∀ x,mapW ρ Prod.fst x≤ H*μ x) → (∀ x,mapW ρ Prod.snd x≤ H*μ x) →
--         (∀ x,ρ x ≤ bp (C*N)*pairW μ μ x) →
--         pr ρ (blackout v T U w ε) ≤ bp (-(1/16:ℝ)*n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HadwigerCounterexample.F`, `OAI.HadwigerCounterexample.Full`, `OAI.HadwigerCounterexample.Inputs`, `OAI.HadwigerCounterexample.IsLaw`, `OAI.HadwigerCounterexample.Keys`, `OAI.HadwigerCounterexample.Knobs`, `OAI.HadwigerCounterexample.Mixer`, `OAI.HadwigerCounterexample.Orient`, `OAI.HadwigerCounterexample.Shape`, `OAI.HadwigerCounterexample.Template`, `OAI.HadwigerCounterexample.UnitType`, `OAI.HadwigerCounterexample.Vec`, `OAI.HadwigerCounterexample.Wgt`, `OAI.HadwigerCounterexample.bp`, `OAI.HadwigerCounterexample.carried`, `OAI.HadwigerCounterexample.freePart`, `OAI.HadwigerCounterexample.fullFintype`, `OAI.HadwigerCounterexample.knFin`, `OAI.HadwigerCounterexample.mapW`, `OAI.HadwigerCounterexample.num`, `OAI.HadwigerCounterexample.orientFintype`, `OAI.HadwigerCounterexample.ownPart`, `OAI.HadwigerCounterexample.pairW`, `OAI.HadwigerCounterexample.pr`, `OAI.HadwigerCounterexample.raw`, `OAI.HadwigerCounterexample.unif`, `OAI.HadwigerCounterexample.Template.blackout` and `OAI.HadwigerCounterexample.Template.chairCut` (definitions bundle `OAIQ430Hc000` of this split).
--
--   **Used by.** The proof of `OAI.HadwigerCounterexample.StatusAnalysis.Quill.sideRelease` of this split imports it.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/HadwigerCounterexample/CutIntegralBounds.lean (declaration OAI.HadwigerCounterexample.Template.shade_calendar)

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
open Finset Real Matrix Function Filter
open scoped BigOperators Topology
variable {p : Shape} {n N M : ℕ} {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]

namespace Template
variable (v : Template p I)

set_option maxHeartbeats 1200000 in
theorem shade_calendar (v : Template p I) (j : I) (M : ℕ) (hM : 1≤M)
    (C ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ n : ℕ in atTop,
      let N := M*n
      ∀ (q : I→F) (U : Wgt (Keys (p:=p) v.t N)) (T : Wgt (Inputs p n I))
        (w : I→Wgt (Knobs p.g n)), (∀ x, |U x|≤1) → chairCut v j U δ →
        carried U (ownPart (p:=p) v.t q) →
        (∀ x, |T x|≤1) → (∀ i,IsLaw (w i)) →
        (∀ i,mapW (w i) (freePart p)=unif) →
      ∀ (m : Mixer p n), 2*num (Full p n)<N →
      let μ:=raw m N; let H:=bp ((1/32:ℝ)*n)
      ∀ (ρ : Wgt (UnitType p n N)), IsLaw ρ →
      (∀ x,mapW ρ Prod.fst x≤ H*μ x) → (∀ x,mapW ρ Prod.snd x≤ H*μ x) →
      (∀ x,ρ x ≤ bp (C*N)*pairW μ μ x) →
      pr ρ (blackout v T U w ε) ≤ bp (-(1/16:ℝ)*n) := by
  sorry
end Template
end HadwigerCounterexample

end

end OAI
end
