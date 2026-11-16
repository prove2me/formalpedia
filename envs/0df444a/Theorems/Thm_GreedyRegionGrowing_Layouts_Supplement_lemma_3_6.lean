-- Prove2me | Theorems.Thm_GreedyRegionGrowing_Layouts_Supplement_lemma_3_6
-- name    : GreedyRegionGrowing.Layouts.Supplement.lemma_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:28:47.287581+00:00
-- url     : https://prove2.me/theorems/c954b674-b0fe-4844-b922-873beb57185a
-- title:
--   Lemma 3.6 — Persistent pointers
-- statement:
--   Fix κ decreasing annuli with endpoints a₀>⋯>aκ. Every F_t is nonincreasing in radius, pointwise nondecreasing in time, and has all values in [1,D]. Consider any finite trace of unit pointer moves starting at 1 and staying in {1,…,κ}, with nondecreasing move times; several moves may have the same time. A move p→p+1 at t is forced by F when F_t(a_p)>2F_t(a_{p−1}). The total number of these forced moves has the following bound, irrespective of the other moves.
--
--   $$
--   \#\{\text{moves forced by }F\}\le\log_2 D.
--   $$
--
--   This is a supporting result for Theorem 1.5.
--
--   Differences from the source:
--   - encoding: finite labelled graphs, ordered iterations and polynomial-time algorithms → Fin n carriers, zero-based trace indices, fixed binary codes and deterministic TM2 polynomial time; reason: labels and iteration shifts change no source instance; the codes include all vertices and rational data, and the machine condition records the full runtime claim
--   - generalization: positive annulus radii a₀ > ⋯ > aκ → arbitrary strictly decreasing real endpoints a₀ > ⋯ > aκ; reason: the forced-move bound uses only their order and the stated monotonicity of F; every source sequence of positive radii is included
-- source:
--   Aditya Anand, Greedy Region Growing: Improved Approximations for Cutwidth, Pathwidth, Flow-Expander Decomposition, and More, STOC 2027 submission #506 (October 2026). Citation basis: published (canonical held submission); 46 pages; printed page = PDF page throughout (offset 0); no arXiv version. Lemma 3.6, p. 19 (PDF p. 19).

import Mathlib
import Definitions.Def_GreedyRegionGrowing_Layouts_Foundation

noncomputable section
open Finset QAlgorithms.Complexity

namespace GreedyRegionGrowing.Layouts.Supplement
attribute [local instance] Classical.propDecidable

/-- Aditya Anand, STOC 2027 submission #506 (October 2026), lemma 3 6. -/
theorem lemma_3_6 (κ L : ℕ) (D : ℝ) (a : ℕ → ℝ) (F : ℕ → ℝ → ℝ)
    (t : Fin L → ℕ) (hκ : L+1 ≤ κ)
    (ha : ∀ i j, i < j → j ≤ κ → a j < a i)
    (hF : ∀ t, Antitone (F t)) (ht : Monotone t)
    (hinc : ∀ t r, F t r ≤ F (t+1) r)
    (hval : ∀ t r, 1 ≤ F t r ∧ F t r ≤ D) :
  ((univ.filter (fun i : Fin L => F (t i) (a (i.val+1)) >
    2*F (t i) (a i.val))).card : ℝ) ≤ Real.logb 2 D := by sorry

end GreedyRegionGrowing.Layouts.Supplement
