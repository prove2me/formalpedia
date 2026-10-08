-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_lemma_2_3
-- name    : LovejoyPOMDP.Monotone.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:57:29.73598+00:00
-- url     : https://prove2.me/theorems/daa351bc-dd57-4787-b032-117eca5baf32
-- title:
--   Lemma 2.3 — sufficient conditions for σ(π, a) to be ≥s-nondecreasing in the action
-- statement:
--   Consider a finite POMDP as in §2 of the paper, with a completely ordered action set $A$. Assume
--
--   1. (a) $a\ge a'$ in $A$ implies $P^a\ge_{tp}P^{a'}$;
--   2. (b) $a\ge a'$ in $A$ implies $r^a(j)\ge_s r^{a'}(j)$ for every $j\in S$;
--   3. (c) $j\ge j'$ in $S$ implies $r^a(j)\ge_s r^a(j')$ for every $a\in A$.
--
--   Then for every belief $\pi\in\Pi(S)$ and all $a\ge a'$ in $A$,
--   $$\sigma(\pi,a)\ \ge_s\ \sigma(\pi,a').$$
--
--   Larger actions make higher observations more likely. In the proof of Proposition 2 this compares the expected continuation values under two actions.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 741, Lemma 2.3

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 741, Lemma 2.3.

If (a) `a ≥ a'` in `A` implies `P^a ≥tp P^{a'}`, (b) `a ≥ a'` in `A` implies
`r^a(j) ≥s r^{a'}(j)` for any `j ∈ S`, and (c) `j ≥ j'` in `S` implies `r^a(j) ≥s r^a(j')` for any
`a ∈ A`, then for all `π ∈ Π(S)` and `a ≥ a'` in `A`, `σ(π, a) ≥s σ(π, a')`. -/
theorem lemma_2_3 {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hP : ∀ a a' : A, a' ≤ a → TPGE (M.P a) (M.P a'))
    (hRa : ∀ a a' : A, a' ≤ a → ∀ j, StochGE (M.R a j) (M.R a' j))
    (hRj : ∀ a (j j' : S), j' ≤ j → StochGE (M.R a j) (M.R a j'))
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) {a a' : A} (haa' : a' ≤ a) :
    StochGE (M.sigma π a) (M.sigma π a') := by sorry

end LovejoyPOMDP.Monotone
