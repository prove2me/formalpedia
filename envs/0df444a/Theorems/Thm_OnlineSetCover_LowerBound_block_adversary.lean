-- Prove2me | Theorems.Thm_OnlineSetCover_LowerBound_block_adversary
-- name    : OnlineSetCover.LowerBound.block_adversary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:05:47.881009+00:00
-- url     : https://prove2.me/theorems/1c92e70e-7c2d-47ed-a553-ab81c9092125
-- title:
--   Section 4 — an adversary forces $kr$ sets on the block family while $\mathrm{OPT} = 1$
-- statement:
--   Let $k, r$ be positive integers and let $\mathcal F$ be the block family of Section 4 on $kr^2$ disjoint blocks of $2^k$ elements. For every valid deterministic online algorithm $A$ for $\mathcal F$ there is a nonempty arrival sequence $\sigma$ of at most $kr$ elements such that
--
--   1. a single set of $\mathcal F$ contains every element of $\sigma$, so $\mathrm{OPT}(\sigma) = 1$, and
--   2. the algorithm has chosen at least $kr$ sets:
--   $$|\mathcal C_A(\sigma)| \;\ge\; kr.$$
--
--   This is the paper's claim that "given any deterministic algorithm, an adversary can choose $kr$ elements in $X$, forcing the algorithm to pick $kr$ sets from $\mathcal F$, while keeping the value of the optimum solution to be 1". It is the core of Proposition 4.2, which adds padding elements and sets to reach arbitrary $n$ and $m$.
--
--   **Formalization Note** The paper's argument tacitly lets the algorithm add one set per arrival; here algorithms may add any number of sets per arrival, and the sequence then may be shorter than $kr$, hence "at most $kr$ elements". The ground set is the blocks only; elements outside the blocks lie in no set and play no role.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 369, Section 4 (unnumbered claim following the definition of F)

import Mathlib
import Definitions.Def_OnlineSetCover_LowerBound_Game
import Definitions.Def_OnlineSetCover_LowerBound_BlockFamily

namespace OnlineSetCover.LowerBound

/-- The adversary claim of §4 (Alon et al. 2009, p. 369): for positive integers `k, r` and every
valid deterministic online algorithm `A` for the block family on the `k r²` blocks of `2^k`
elements, there is a nonempty arrival sequence of at most `k r` elements that a single set of
the family covers (so `OPT = 1`), on which `A` chooses at least `k r` sets. -/
theorem block_adversary (k r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (A : OnlineAlg (Fin (k * r ^ 2) × Fin (2 ^ k))) (hA : IsValid (blockFamily k r) A) :
    ∃ σ : List (Fin (k * r ^ 2) × Fin (2 ^ k)), σ ≠ [] ∧ σ.length ≤ k * r ∧
      (∃ S ∈ blockFamily k r, ∀ x ∈ σ, x ∈ S) ∧ k * r ≤ cost A σ := by sorry

end OnlineSetCover.LowerBound
