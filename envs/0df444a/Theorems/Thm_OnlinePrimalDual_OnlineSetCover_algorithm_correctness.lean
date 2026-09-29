-- Prove2me | Theorems.Thm_OnlinePrimalDual_OnlineSetCover_algorithm_correctness
-- name    : OnlinePrimalDual.OnlineSetCover.algorithm_correctness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T05:40:49.862621+00:00
-- url     : https://prove2.me/theorems/0d26f711-4212-4d4a-ae86-c4f17615ead1
-- title:
--   Theorem 5.2 — the deterministic algorithm's guarantee (goal)
-- statement:
--   Given the potential-function invariant `Φ < n²` that Lemma 5.1 maintains throughout a run for
--   a fixed guess `α ≥ c(COPT)`, and that the fractional subroutine's solution is `β`-competitive
--   (`∑ wscs ≤ βα`, the book's `O(log m)`-competitive input, Section 4): (i) every element of
--   weight `≥ 1` is covered; (ii) the total cost of the chosen cover is at most `α·log n·(3β+2)`,
--   i.e. `α·O(log n)` for the `β = O(log m)` the book's own Section-4 fractional algorithms supply.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 139, Theorem 5.2

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential

namespace OnlinePrimalDual.OnlineSetCover

/-- **Theorem 5.2** (p. 139, PDF p. 50) — the goal of this mission. Characterizes any state
`(w, C)` reached by the deterministic online algorithm for a single guess `α ≥ c(COPT)` via the
potential-function invariant `Φ < n²` that Lemma 5.1 (together with the initial value
`Φ ≤ n·n⁰+n < n²`, proof, p. 139) maintains throughout the run, plus the book's own external
input "the fractional solution is `O(log m)`-competitive" (p. 136: "an online algorithm that
generates an `O(log m)`-competitive fractional solution, e.g., the online fractional algorithm
presented in Section 4"), taken here as an explicit ratio `β` rather than the specific constant of
whichever Section-4 algorithm is plugged in as the subroutine (see `STATUS.md`/`MODERATION_NOTES.md`
for the choice). (i) is the book's part (i) verbatim (every element of weight `≥1` is covered).
(ii) is the book's part (ii) with the `O(log m log n)` made explicit as `log n·(3β+2)`: the book's
own proof derives `∑ csχC(s) ≤ ∑3wscs log n + 2α log n` from the same invariant (displayed
inequality, p. 139-140), and "the desired result follows from the fact that the fractional
solution is `O(log m)`-competitive" substitutes `∑ wscs ≤ βα` (since `α ≥ c(COPT)`), giving
`∑csχC(s) ≤ 3βα log n + 2α log n = α log n(3β+2)`. -/
theorem algorithm_correctness {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α β : ℝ) (hα_pos : 0 < α) (hβ_nonneg : 0 ≤ β)
    (w : T → ℝ) (hw_nonneg : ∀ t, 0 ≤ w t) (C : Finset T)
    (hE : 1 ≤ Fintype.card E)
    (hfrac : ∑ t : T, w t * inst.c t ≤ β * α)
    (hΦ_bound : potential inst w C α < (Fintype.card E : ℝ) ^ 2) :
    (∀ e : E, 1 ≤ elementWeight inst w e → coveredBy inst C e) ∧
    (∑ t ∈ C, inst.c t ≤ α * Real.log (Fintype.card E : ℝ) * (3 * β + 2)) := by sorry

end OnlinePrimalDual.OnlineSetCover
