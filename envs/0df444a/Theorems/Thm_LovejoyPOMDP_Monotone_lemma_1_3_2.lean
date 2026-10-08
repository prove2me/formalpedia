-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_lemma_1_3_2
-- name    : LovejoyPOMDP.Monotone.lemma_1_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:56:57.746609+00:00
-- url     : https://prove2.me/theorems/6a606d9a-e4ef-40b1-a614-3c2023640867
-- title:
--   Lemma 1.3, part 2 — if a ≥ a′ implies P^a ≥tp P^{a′}, then πP^a ≥r πP^{a′}
-- statement:
--   Consider a finite POMDP as in §2 of the paper, with a completely ordered action set $A$. Suppose that $a\ge a'$ in $A$ implies $P^a\ge_{tp}P^{a'}$. Then for every belief $\pi\in\Pi(S)$ and all $a\ge a'$ in $A$,
--   $$\pi P^a\ \ge_r\ \pi P^{a'}.$$
--
--   Larger actions thus push the predicted state distribution up in the likelihood ratio order. This is hypothesis (a) of Lemma 1.2(3) and enters the proof of Lemma 2.3.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, Lemma 1.3, part 2

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, Lemma 1.3, part 2.

If `a ≥ a'` in `A` implies `P^a ≥tp P^{a'}`, then `π ∈ Π(S)` and `a ≥ a'` imply
`πP^a ≥r πP^{a'}`. -/
theorem lemma_1_3_2 {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hP : ∀ a a' : A, a' ≤ a → TPGE (M.P a) (M.P a')) {π : S → ℝ}
    (hπ : π ∈ stdSimplex ℝ S) {a a' : A} (haa' : a' ≤ a) :
    MLRGE (M.predict π a) (M.predict π a') := by sorry

end LovejoyPOMDP.Monotone
