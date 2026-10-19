-- Prove2me | Theorems.Thm_InfFisher_Linear_lemma_7
-- name    : InfFisher.Linear.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:40.951034+00:00
-- url     : https://prove2.me/theorems/b645af1a-8300-4d0a-804b-ff7e2efa434a
-- title:
--   Lemma 7, p. 15 — ordered intervals dominate feasible utilities
-- statement:
--   Let $n\ge1$ and let the buyer valuations $v_i(\theta)=c_i\theta+d_i$ on $[0,1]$ satisfy $c_i/2+d_i=1$ and $2\ge d_1\ge\cdots\ge d_n\ge0$. Every feasible utility vector $u\in U(v,[0,1])$ is coordinatewise bounded by the utilities of an ordered partition into possibly empty intervals:
--
--   $$0=a_0\le a_1\le\cdots\le a_n=1,\qquad u_i\le\int_{a_{i-1}}^{a_i}v_i(\theta)\,d\theta\quad(i=1,\ldots,n).$$
--
--   This replaces an arbitrary fractional allocation by an ordered interval allocation that gives at least the requested utility to each buyer.
--
--   **Formalization Note** The requirement $n\ge1$ makes the two endpoint equations consistent. Lean buyer $i$ corresponds to the paper's buyer $i+1$.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Lemma 7, p. 15

import Mathlib
import Definitions.Def_InfFisher_Linear_Setting

namespace InfFisher.Linear

open MeasureTheory

/-- Gao–Kroer, Lemma 7: ordered intervals can dominate every feasible utility vector. -/
theorem lemma_7 {n : ℕ} (hn : 0 < n) (c d : ℕ → ℝ)
    (hnorm : ∀ i < n, c i / 2 + d i = 1)
    (hd : ∀ i j, i ≤ j → j < n → d j ≤ d i)
    (hd2 : d 0 ≤ 2) (hd0 : 0 ≤ d (n - 1)) :
    ∀ u ∈ feasUtil (volume.restrict (Set.Icc (0 : ℝ) 1)) (linVal c d n),
      ∃ a : ℕ → ℝ, a 0 = 0 ∧
        (∀ k < n, a k ≤ a (k + 1)) ∧ a n = 1 ∧
        ∀ i : Fin n, u i ≤ ∫ θ in Set.Icc (a i.val) (a (i.val + 1)),
          (c i.val * θ + d i.val) := by sorry

end InfFisher.Linear
