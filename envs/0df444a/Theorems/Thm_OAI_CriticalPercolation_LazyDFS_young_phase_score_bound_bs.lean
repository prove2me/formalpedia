-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_LazyDFS_young_phase_score_bound_bs
-- name    : OAI.CriticalPercolation.LazyDFS.young_phase_score_bound_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:36:10.503612+00:00
-- url     : https://prove2.me/theorems/5389ea3c-11a1-478b-bb0d-0389357e0ee9
-- title:
--   OAI.CriticalPercolation.LazyDFS.young_phase_score_bound_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.LazyDFS.young_phase_score_bound` of [lean/OAI/Probability/CriticalPercolation/Exploration/ListScore.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Exploration/ListScore.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.LazyDFS`, with `open Set MeasureTheory ProbabilityTheory`, `open Set`, `open scoped BigOperators`, `open scoped Classical`, `open scoped Classical`, `open FiniteProduct SearchTree`):
--
--   ```lean
--   theorem young_phase_score_bound_bs (G : BondGraph V E) (order : List (Dart V E))
--       (B : Set V) (f : E) (a s t : V) (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
--       {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (fuel : ℕ) (st : State V E)
--       (hf : f ∈ st.read) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
--       (hn : ∀ e b, 0 ≤ w e b) (fresh : Fresh w p st.read) :
--       let H := G.eraseBond f a
--       let T := compile G order B fuel st (push G order s)
--       expect w (fun ω => if H.joinedPair a s t ω then T.score p (H.wiredEvent a s t) w ω else 0) ≤
--         prob w (H.joinedPair a s t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.SearchTree`, `OAI.CriticalPercolation.BondGraph.eraseBond`, `OAI.CriticalPercolation.BondGraph.joinedPair`, `OAI.CriticalPercolation.BondGraph.wiredEvent`, `OAI.CriticalPercolation.FiniteProduct.expect`, `OAI.CriticalPercolation.FiniteProduct.prob`, `OAI.CriticalPercolation.LazyDFS.Dart`, `OAI.CriticalPercolation.LazyDFS.State`, `OAI.CriticalPercolation.LazyDFS.compile` and `OAI.CriticalPercolation.LazyDFS.push` (definitions bundle `OAIQ078B000` of this split); `OAI.CriticalPercolation.LazyDFS.Fresh` (definitions bundle `OAIQ078B001` of this split); `OAI.CriticalPercolation.SearchTree.score` (definitions bundle `OAIQ078B002` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.ExactExposure.marked_pair_bound_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Exploration/ListScore.lean (declaration OAI.CriticalPercolation.LazyDFS.young_phase_score_bound)

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
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem young_phase_score_bound_bs (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (f : E) (a s t : V) (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (fuel : ℕ) (st : State V E)
    (hf : f ∈ st.read) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (fresh : Fresh w p st.read) :
    let H := G.eraseBond f a
    let T := compile G order B fuel st (push G order s)
    expect w (fun ω => if H.joinedPair a s t ω then T.score p (H.wiredEvent a s t) w ω else 0) ≤
      prob w (H.joinedPair a s t) := by
  sorry

end CriticalPercolation.LazyDFS

end
end

end OAI
end
