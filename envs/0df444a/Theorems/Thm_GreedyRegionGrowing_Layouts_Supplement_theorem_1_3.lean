-- Prove2me | Theorems.Thm_GreedyRegionGrowing_Layouts_Supplement_theorem_1_3
-- name    : GreedyRegionGrowing.Layouts.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:27:32.713521+00:00
-- url     : https://prove2.me/theorems/fdf2b1df-6340-4a03-a519-f6531a3ac695
-- title:
--   Theorem 1.3 — Treedepth approximation
-- statement:
--   On every finite simple undirected graph, a deterministic polynomial-time algorithm returns an elimination forest F on all its vertices. The height is exactly n when n≤1. For all n≥2 it obeys the bound below, with an absolute constant fixed before the graph. Neither connectivity nor a positive optimum is required.
--
--   $$
--   \operatorname{height}(F)\le C\log n\,\operatorname{td}(G)\quad(n\ge2).
--   $$
--
--   This is a companion result of the layout mission.
--
--   Differences from the source:
--   - encoding: finite labelled graphs, ordered iterations and polynomial-time algorithms → Fin n carriers, zero-based trace indices, fixed binary codes and deterministic TM2 polynomial time; reason: labels and iteration shifts change no source instance; the codes include all vertices and rational data, and the machine condition records the full runtime claim
--   - encoding: O(log n) treedepth bound → the logarithmic bound for n≥2 and exact height n for n≤1; reason: the asymptotic bound leaves these finitely many sizes unspecified; a singleton has height 1 although log 1=0
-- source:
--   Aditya Anand, Greedy Region Growing: Improved Approximations for Cutwidth, Pathwidth, Flow-Expander Decomposition, and More, STOC 2027 submission #506 (October 2026). Citation basis: published (canonical held submission); 46 pages; printed page = PDF page throughout (offset 0); no arXiv version. Theorem 1.3, p. 6 (PDF p. 6).

import Mathlib
import Definitions.Def_GreedyRegionGrowing_Layouts_Foundation

noncomputable section
open Finset QAlgorithms.Complexity

namespace GreedyRegionGrowing.Layouts.Supplement
attribute [local instance] Classical.propDecidable

/-- Aditya Anand, STOC 2027 submission #506 (October 2026), theorem 1 3. -/
theorem theorem_1_3 :
  ∃ C : ℝ, 0 < C ∧ ∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ p : Parent n,
      f (graphCode G) = parentCode p ∧ EliminationForest G univ p ∧
      (n ≤ 1 → forestHeight univ p = n) ∧
      (2 ≤ n → (forestHeight univ p : ℝ) ≤ C*Real.log n*treedepth G univ) := by sorry

end GreedyRegionGrowing.Layouts.Supplement
