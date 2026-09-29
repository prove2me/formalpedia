-- Prove2me | Theorems.Thm_MarkovMixing_biased_walk_cutoff
-- name    : MarkovMixing.biased_walk_cutoff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:27:36.348652+00:00
-- url     : https://prove2.me/theorems/8994b795-1388-44dd-b2d6-2ed58f4a8eb9
-- title:
--   Biased walk cutoff at $\beta^{-1}n$ with window $\sqrt n$
-- statement:
--   The **lazy biased random walk** on the segment $\{0,1,\dots,n\}$ with up-probability $p>\tfrac12$ moves as follows: from an interior state, hold with probability $\tfrac12$, step up with probability $p/2$, step down with probability $(1-p)/2$; at each endpoint, hold with probability $\tfrac12$ and step inward with probability $\tfrac12$. Write $\beta=p-\tfrac12$ for the bias, $\pi_n$ for the stationary distribution (which weights the top of the segment geometrically), and $d_n(t)=\max_x\|P^t_n(x,\cdot)-\pi_n\|_{TV}$ for the worst-case total variation distance. A family has a **cutoff at $t_n$ with window $w_n$** when $w_n/t_n\to0$ and $d_n(\lfloor t_n+\alpha w_n\rfloor)$ tends (liminf/limsup over $n$) to $1$ as $\alpha\to-\infty$ and to $0$ as $\alpha\to+\infty$.
--
--   The theorem (Theorem 18.2 of Levin–Peres–Wilmer) asserts: the family has a cutoff at
--   $$t_n=\beta^{-1}n\qquad\text{with window}\qquad w_n=\sqrt n.$$
--
--   The mechanism is transparent: the walk must travel distance $n$ against a deterministic drift of speed $\beta$, taking time $\beta^{-1}n$, with diffusive fluctuations of order $\sqrt n$ around it — the cutoff time is a law of large numbers and the window a central limit theorem. This is the simplest chain exhibiting a genuine cutoff, and the book's warm-up for the hypercube.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 18.2.1, Theorem 18.2, p. 249

import Definitions.Def_mm_cutoff
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace MarkovMixing

/-- **Theorem 18.2** (LPW): the lazy biased random walk on `{0,…,n}` with
bias `β = p − 1/2 > 0` has a cutoff at `β⁻¹ n` with a window of order
`√n`. -/
theorem biased_walk_cutoff (p : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1)
    (π : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hπ : ∀ n, 0 < n → IsStationary (biasedSegmentWalk n p) (π n)) :
    HasCutoffWindow (fun n => biasedSegmentWalk n p) π
      (fun n => (p - 1 / 2)⁻¹ * n) (fun n => Real.sqrt n) := by
  sorry

end MarkovMixing
