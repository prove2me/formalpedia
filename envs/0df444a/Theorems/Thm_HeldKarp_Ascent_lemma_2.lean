-- Prove2me | Theorems.Thm_HeldKarp_Ascent_lemma_2
-- name    : HeldKarp.Ascent.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T06:30:13.876964+00:00
-- url     : https://prove2.me/theorems/a9121941-e8cc-4a9e-afb3-b050ca73e3dc
-- title:
--   Lemma 2: a step $0 < t < 2(w(\bar\pi)-w(\pi))/\|v_{k(\pi)}\|^2$ moves strictly closer to $\bar\pi$
-- statement:
--   Let $n \ge 3$, let $(c_{ij})$ be symmetric real edge weights on $K_n$, let $w$ be the 1-tree bound, and let $\|\cdot\|$ denote the Euclidean norm on $\mathbb R^n$. Let $\pi, \bar\pi \in \mathbb R^n$ and let $k(\pi)$ be any minimum-weight 1-tree at $\pi$, with degree-excess vector $v_{k(\pi)}$. If
--   $$0 < t < \frac{2\,(w(\bar\pi) - w(\pi))}{\|v_{k(\pi)}\|^2},$$
--   then
--   $$\|\bar\pi - (\pi + t\,v_{k(\pi)})\| < \|\bar\pi - \pi\|.$$
--
--   So a step of the iteration (3) with a suitably small positive step size moves strictly closer to every point with a larger value of $w$, in particular to every maximizer of $w$. This is the rationale for the choice of step sizes in the ascent method.
--
--   **Formalization Note** Both sides are compared through squared Euclidean norms, written as sums of squares (equivalent, since the square root is strictly increasing). If $v_{k(\pi)} = 0$ the right-hand bound is $0$ in Lean (division by zero), so the hypothesis cannot hold; in the paper $v_{k(\pi)} = 0$ only at a maximizer of $w$, where it cannot hold either.
-- source:
--   Held & Karp, The traveling-salesman problem and minimum spanning trees: Part II, Math. Programming 1 (1971), DOI 10.1007/BF01584070, §2, p. 9 (PDF p. 4), Lemma 2 and its footnote (Euclidean norm)

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound

namespace HeldKarp.Ascent

/-- **Lemma 2** — Held & Karp, *The traveling-salesman problem and minimum spanning trees: Part II*,
Math. Programming 1 (1971), §2, p. 9 (PDF p. 4): "If 0 < t < 2(w(π̄) − w(π)) / ‖v_{k(π)}‖² then
‖π̄ − (π + t v_{k(π)})‖ < ‖π̄ − π‖", where "‖ ‖ denotes Euclidean norm" (footnote, p. 9).

Here `G` is any minimum-weight 1-tree at the point `π` (the paper's `k(π)`).

Formalization Note: both sides are compared through squared Euclidean norms, written as sums of
squares (the square root is strictly monotone, so this is equivalent). Mathlib's `‖·‖` on
`Fin n → ℝ` is the sup norm and is not used. If `‖v_{k(π)}‖² = 0`, Lean's division gives
`2(w(π̄) − w(π)) / 0 = 0` and the hypothesis `0 < t < 0` is unsatisfiable; in the paper
`v_{k(π)} = 0` only when `π` maximizes `w`, where the hypothesis cannot hold either. `3 ≤ n`
is implicit in the paper. -/
theorem lemma_2 {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (πbar π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c π G) (t : ℝ) (ht : 0 < t)
    (ht' : t < 2 * (oneTreeBound c πbar - oneTreeBound c π) / ∑ i, (degExcess G i) ^ 2) :
    ∑ i, (πbar i - (π i + t * degExcess G i)) ^ 2 < ∑ i, (πbar i - π i) ^ 2 := by sorry

end HeldKarp.Ascent
