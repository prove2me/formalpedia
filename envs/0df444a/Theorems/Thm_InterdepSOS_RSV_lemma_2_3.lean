-- Prove2me | Theorems.Thm_InterdepSOS_RSV_lemma_2_3
-- name    : InterdepSOS.RSV.lemma_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:30.496484+00:00
-- url     : https://prove2.me/theorems/f6af4055-ea07-44a3-b6da-665adeb65b8c
-- title:
--   Lemma 2.3, p. 12 — simultaneous signal increments preserve the d-SOS bound
-- statement:
--   Let $v$ be a nonnegative $d$-SOS function on nonnegative signal profiles. Partition the coordinates into $A$ and its complement $B$. Hold the coordinates in $A$ at $s_A$, then increase them by the nonnegative vector $y_A$. If $s_B\le s'_B$ coordinatewise, the gain at the higher complementary profile is bounded by $d$ times the gain at the lower one:
--
--   $$
--   v(s_A+y_A,s'_B)-v(s_A,s'_B)\le d\bigl(v(s_A+y_A,s_B)-v(s_A,s_B)\bigr).
--   $$
--
--   The lemma extends the one-coordinate $d$-SOS condition to simultaneous changes in any chosen set of coordinates.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), p. 12, Lemma 2.3

import Mathlib
import Definitions.Def_InterdepSOS_RSV_Setting

namespace InterdepSOS.RSV

theorem lemma_2_3 {n : ℕ} (w : Signal n → ℝ) (hw : ∀ s, 0 ≤ w s)
    (d : ℝ) (hd : IsDSOS d w) (A : Finset (Fin n))
    (s y s' : Signal n) (hss' : ∀ j, j ∉ A → s j ≤ s' j) :
    w (fun j => if j ∈ A then s j + y j else s' j) -
      w (fun j => if j ∈ A then s j else s' j) ≤
      d * (w (fun j => if j ∈ A then s j + y j else s j) - w s) := by sorry

end InterdepSOS.RSV
