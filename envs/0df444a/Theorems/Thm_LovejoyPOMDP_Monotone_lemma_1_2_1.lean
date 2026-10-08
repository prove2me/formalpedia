-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_lemma_1_2_1
-- name    : LovejoyPOMDP.Monotone.lemma_1_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:56:35.253584+00:00
-- url     : https://prove2.me/theorems/8c4b69b9-6aba-4bf8-b90f-0c178fd648dc
-- title:
--   Lemma 1.2, part 1 (“if” direction) — MLR-ordered observation rows make T(π, a, k) MLR-nondecreasing in k
-- statement:
--   Consider a finite POMDP as in §2 of the paper, with $r^a_{jk}>0$, and fix an action $a\in A$. If the rows of the observation matrix are MLR-ordered,
--   $$r^a(j)\ \ge_r\ r^a(j')\qquad\text{for all } j\ge j' \text{ in } S,$$
--   then for every belief $\pi\in\Pi(S)$ the Bayes update is MLR-nondecreasing in the observation:
--   $$T(\pi,a,k)\ \ge_r\ T(\pi,a,k')\qquad\text{for all } k\ge k' \text{ in } O.$$
--
--   Higher observations are evidence for higher states. This is the step of the proofs of Propositions 1 and 2 that makes $k\mapsto V(T(\pi,a,k))$ nondecreasing.
--
--   **Formalization Note** The paper states this part as "if and only if". The "only if" direction is false as printed: with $n=m=2$, both rows of $P^a$ equal to $(1,0)$ and $r^a(1)=(0.1,0.9)$, $r^a(2)=(0.9,0.1)$, every posterior is $(1,0)$, so the conclusion holds while $r^a(2)\ge_r r^a(1)$ fails. Only the "if" direction is stated; it is the direction the paper uses.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 738, Lemma 1.2, part 1 (the "if" direction)

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 738, Lemma 1.2, part 1 — the "if" direction.

Fix `a ∈ A`. If `r^a(j) ≥r r^a(j')` for all `j ≥ j'` in `S`, then for every `π ∈ Π(S)`,
`T(π, a, k) ≥r T(π, a, k')` for all `k ≥ k'` in `O`.

**Formalization Note.** The paper states "if and only if". The "only if" direction is false as
printed: with `n = m = 2`, both rows of `P^a` equal to `(1, 0)`, `T(π, a, k) = (1, 0)` for every
`π` and `k`, so the left side holds, while `r^a(1) = (0.1, 0.9)`, `r^a(2) = (0.9, 0.1)` violate
`r^a(2) ≥r r^a(1)`. Only the "if" direction is stated; it is the direction used in the proofs of
Propositions 1 and 2. -/
theorem lemma_1_2_1 {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A) (a : A)
    (hR : ∀ j j' : S, j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) {k k' : O} (hkk' : k' ≤ k) :
    MLRGE (M.bayes π a k) (M.bayes π a k') := by sorry

end LovejoyPOMDP.Monotone
