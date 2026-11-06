-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_consecutive_stages_slide
-- name    : KawasakiSOS.Threshold.consecutive_stages_slide
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:03:28.319359+00:00
-- url     : https://prove2.me/theorems/cf16a2e3-2b69-481d-84e7-0ee04a4fe26b
-- title:
--   Lemma 4.8: consecutive stages differ by a slide
-- statement:
--   Let $k\ge6$ and let two consecutive site pairs give stages $S$ and $S'$ via (6). Then either $S=S'$, or $S'$ is obtained from $S$ by one of the following slides:
--
--   1. an A-slide: $c_A$ changes by $\pm1$ and $c_B$ is fixed;
--   2. a B-slide: $c_B$ changes by $\pm1$ and $c_A$ is fixed;
--   3. a block slide: both centers change by the same $\pm1$, and $U=\emptyset$ in both $S$ and $S'$, or $T=\emptyset$ in both.
--
--   In each case exactly one site $u\notin W$ enters $W'=W_A'\cup W_B'$, and exactly one site $v\in W$ leaves it.
--
--   So the canonical path changes the windows by one site at a time.
--
--   Differences from the source:
--   - generalization: two consecutive site pairs of the climbers → any two pairs with s_a ≤ s_b ≤ k − 1 differing by ±1 in exactly one coordinate, for any base column p0; reason: the proof uses only these properties, and the pairs of a site sequence satisfy them
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.8, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_Stage
import Definitions.Def_KawasakiSOS_Threshold_stageOf
import Definitions.Def_KawasakiSOS_Threshold_IsSlide
import Definitions.Def_KawasakiSOS_Threshold_IsAdjacentPair

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 4.8, p. 12 (PDF p. 13).

Formalization Notes:
- generalization: two consecutive site pairs of the climbers → any two pairs with s_a ≤ s_b ≤ k − 1 differing by ±1 in exactly one coordinate, for any base column p0. The proof uses only these properties, and the pairs of a site sequence satisfy them. -/
theorem consecutive_stages_slide {k : ℕ} [NeZero k] (hk : 6 ≤ k) (p0 : ZMod k) (q q' : ℕ × ℕ) (hq : q.1 ≤ q.2) (hq' : q'.1 ≤ q'.2) (hqk : q.2 ≤ k - 1) (hqk' : q'.2 ≤ k - 1) (hadj : IsAdjacentPair q q') :
    stageOf k p0 q'.1 q'.2 = stageOf k p0 q.1 q.2 ∨
      IsSlide (stageOf k p0 q.1 q.2) (stageOf k p0 q'.1 q'.2) := by sorry

end KawasakiSOS.Threshold
