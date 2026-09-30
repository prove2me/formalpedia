-- Prove2me | Theorems.Thm_HeldKarp_Ascent_lemma_1
-- name    : HeldKarp.Ascent.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T06:19:22.804862+00:00
-- url     : https://prove2.me/theorems/0c4a50d6-1445-43ae-ba14-09a964d7e239
-- title:
--   Lemma 1: $(\bar\pi - \pi)\cdot v_{k(\pi)} \ge w(\bar\pi) - w(\pi) \ge 0$
-- statement:
--   Let $n \ge 3$, let $(c_{ij})$ be symmetric real edge weights on $K_n$, and let $w$ be the 1-tree bound. Let $\pi, \bar\pi \in \mathbb R^n$ satisfy $w(\bar\pi) \ge w(\pi)$, and let $k(\pi)$ be any minimum-weight 1-tree at the point $\pi$, with degree-excess vector $v_{k(\pi)}$. Then
--   $$(\bar\pi - \pi)\cdot v_{k(\pi)} \;\ge\; w(\bar\pi) - w(\pi) \;\ge\; 0.$$
--
--   Geometrically, the hyperplane through $\pi$ with normal $v_{k(\pi)}$ bounds a closed half-space containing every point $\bar\pi$ at least as good as $\pi$, in particular every maximizer of $w$: $v_{k(\pi)}$ is a supergradient of the concave function $w$ at $\pi$. This justifies stepping from $\pi$ along $v_{k(\pi)}$.
--
--   **Formalization Note** The inner product is Euclidean, written as a coordinate sum. The minimum-weight 1-tree may be any of the tied minimizers.
-- source:
--   Held & Karp, The traveling-salesman problem and minimum spanning trees: Part II, Math. Programming 1 (1971), DOI 10.1007/BF01584070, §2, p. 9 (PDF p. 4), Lemma 1

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound

namespace HeldKarp.Ascent

/-- **Lemma 1** — Held & Karp, *The traveling-salesman problem and minimum spanning trees: Part II*,
Math. Programming 1 (1971), §2, p. 9 (PDF p. 4): "Let π̄ and π be such that w(π̄) ≥ w(π). Then
(π̄ − π) · v_{k(π)} ≥ w(π̄) − w(π) ≥ 0."

Here `G` plays the role of the 1-tree `k(π)`: any minimum-weight 1-tree at the point `π`.

Formalization Note: `·` is the Euclidean inner product, written as a sum over coordinates. The
choice of minimum-weight 1-tree is arbitrary among ties (every choice is covered). `3 ≤ n` is
implicit in the paper (1-trees exist only for `n ≥ 3`). -/
theorem lemma_1 {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (πbar π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c π G)
    (hw : oneTreeBound c π ≤ oneTreeBound c πbar) :
    oneTreeBound c πbar - oneTreeBound c π ≤ ∑ i, (πbar i - π i) * degExcess G i ∧
      0 ≤ oneTreeBound c πbar - oneTreeBound c π := by sorry

end HeldKarp.Ascent
