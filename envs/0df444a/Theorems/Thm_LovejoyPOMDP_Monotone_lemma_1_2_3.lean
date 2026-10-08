-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_lemma_1_2_3
-- name    : LovejoyPOMDP.Monotone.lemma_1_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:56:51.919002+00:00
-- url     : https://prove2.me/theorems/4adc5a96-6d5f-4bbe-9d14-eb21a241008c
-- title:
--   Lemma 1.2, part 3 — sufficient conditions for T(π, a, k) to be MLR-nondecreasing in the action
-- statement:
--   Consider a finite POMDP as in §2 of the paper, with a completely ordered action set $A$. Fix a belief $\pi\in\Pi(S)$ and an observation $k\in O$. Suppose that for all $a\ge a'$ in $A$:
--
--   1. $\pi P^a\ge_r\pi P^{a'}$, and
--   2. $r^a_{jk}\,r^{a'}_{j'k}\ \ge\ r^{a'}_{jk}\,r^a_{j'k}$ for all $j\ge j'$ in $S$.
--
--   Then
--   $$T(\pi,a,k)\ \ge_r\ T(\pi,a',k)\qquad\text{for all } a\ge a' \text{ in } A.$$
--
--   After observing $k$, the posterior obtained under a larger action is larger in the likelihood ratio order. This is the step of Proposition 2's proof that compares continuation values across actions.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, Lemma 1.2, part 3

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, Lemma 1.2, part 3.

For any `π ∈ Π(S)` and `k ∈ O`: `T(π, a, k) ≥r T(π, a', k)` for all `a ≥ a'` in `A` if for all such
`a` and `a'`: (a) `πP^a ≥r πP^{a'}`; (b) `r^a_{jk} r^{a'}_{j'k} ≥ r^{a'}_{jk} r^a_{j'k}` for all
`j ≥ j'` in `S`. -/
theorem lemma_1_2_3 {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (k : O)
    (ha : ∀ a a' : A, a' ≤ a → MLRGE (M.predict π a) (M.predict π a'))
    (hb : ∀ a a' : A, a' ≤ a → ∀ j j' : S, j' ≤ j →
      M.R a' j k * M.R a j' k ≤ M.R a j k * M.R a' j' k) :
    ∀ a a' : A, a' ≤ a → MLRGE (M.bayes π a k) (M.bayes π a' k) := by sorry

end LovejoyPOMDP.Monotone
