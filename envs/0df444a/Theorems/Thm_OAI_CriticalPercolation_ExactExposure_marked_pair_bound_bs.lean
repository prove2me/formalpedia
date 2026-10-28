-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_ExactExposure_marked_pair_bound_bs
-- name    : OAI.CriticalPercolation.ExactExposure.marked_pair_bound_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:34:58.830461+00:00
-- url     : https://prove2.me/theorems/350b5748-f252-4eef-845f-c061240c91a7
-- title:
--   OAI.CriticalPercolation.ExactExposure.marked_pair_bound_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.ExactExposure.marked_pair_bound` of [lean/OAI/Probability/CriticalPercolation/Exploration/PrefixScoreNonneg.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Exploration/PrefixScoreNonneg.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.ExactExposure`, with `open Set MeasureTheory ProbabilityTheory`, `open Real`, `open Set Real`, `open scoped Topology`, `open scoped BigOperators`, `open Set`, `open Set MeasureTheory`, `open Set MeasureTheory Real`, `open scoped Interval`, `open scoped Classical`, `open scoped Classical`, `open FiniteProduct SearchTree LazyDFS`):
--
--   ```lean
--   theorem marked_pair_bound_bs (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
--       (horder : LazyDFS.GoodDarts G order) (ho : LazyDFS.Exhaustive G order)
--       (B : Set V) (a b : V) (hb : b ∈ B) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
--       (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
--       expect (QueryTree.bitWeight p) (fun ω => ∑ f,
--         markWeight G order B a b p w ω f * (1 + markCost G order B a b p w ω f)) ≤ 4
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.ExactExposure.markCost`, `OAI.CriticalPercolation.ExactExposure.markWeight`, `OAI.CriticalPercolation.FiniteProduct.expect`, `OAI.CriticalPercolation.LazyDFS.Dart` and `OAI.CriticalPercolation.QueryTree.bitWeight` (definitions bundle `OAIQ078B000` of this split); `OAI.CriticalPercolation.LazyDFS.Exhaustive` and `OAI.CriticalPercolation.LazyDFS.GoodDarts` (definitions bundle `OAIQ078B002` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Exploration/PrefixScoreNonneg.lean (declaration OAI.CriticalPercolation.ExactExposure.marked_pair_bound)

import Mathlib
import Definitions.Def_OAIQ078B002

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*} [Fintype V] [Fintype E]

theorem marked_pair_bound_bs (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (horder : LazyDFS.GoodDarts G order) (ho : LazyDFS.Exhaustive G order)
    (B : Set V) (a b : V) (hb : b ∈ B) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    expect (QueryTree.bitWeight p) (fun ω => ∑ f,
      markWeight G order B a b p w ω f * (1 + markCost G order B a b p w ω f)) ≤ 4 := by
  sorry

end CriticalPercolation.ExactExposure

end
end

end OAI
end
