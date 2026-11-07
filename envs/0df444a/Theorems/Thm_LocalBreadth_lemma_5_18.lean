-- Prove2me | Theorems.Thm_LocalBreadth_lemma_5_18
-- name    : LocalBreadth.lemma_5_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:54:11.970549+00:00
-- url     : https://prove2.me/theorems/22f61e4f-108a-4399-a352-72e596f40013
-- title:
--   Lemma 5.18 — the local pairing game
-- statement:
--   Let a finite board $B$ be revealed through an increasing filtration $\emptyset=Y_0\subseteq Y_1\subseteq\dots\subseteq Y_m=B$, and put $d_i=|Y_i\setminus Y_{i-1}|$. On each turn the adversary selects a visible point, with repetitions allowed, and the algorithm selects an unused visible point if one remains. Other events may also select unused points of $B$ for the algorithm, whether or not visible. If every point of $B$ is eventually selected by the adversary, the final number of algorithm-selected points is at least
--   $$\sum_{i=1}^m\Bigl\lfloor\frac{d_i}2\Bigr\rfloor.$$
--
--   Differences from the source:
--   - encoding: the game described in prose → legal logs `GameRun` built from the moves of `GameStep`, with the level of the filtration in the position; reason: each move of the page is one constructor; the log need not reveal levels after every point has been selected, since those increments are then zero
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Lemma 5.18, p.36

import Mathlib
import Definitions.Def_LocalBreadth_GameRun

namespace LocalBreadth

/-- Lemma 5.18 (Local pairing game). Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…),
p.36. A finite board `B` is revealed through an increasing filtration `∅ = Y 0 ⊆ ⋯ ⊆ Y m = B`, with
`d_i = |Y i \ Y (i − 1)|`. If every point of `B` is eventually selected by the adversary, the final number of
algorithm-selected points is at least `Σ_i ⌊d_i/2⌋`.

**Formalization Note.** The rules are the legal moves of `GameStep`, applied along a legal log. -/
theorem lemma_5_18 (B : Finset ℤ) (m : ℕ) (Y : ℕ → Finset ℤ) (hY0 : Y 0 = ∅)
    (hmono : ∀ i < m, Y i ⊆ Y (i + 1)) (hYm : Y m = B)
    (log : List GameEvent) (s : GameState) (hrun : GameRun B Y m log s)
    (hcomplete : ∀ y ∈ B, ∃ r, GameEvent.turn y r ∈ log) :
    ∑ i ∈ Finset.range m, (Y (i + 1) \ Y i).card / 2 ≤ s.white.card := by sorry

end LocalBreadth
