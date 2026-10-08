-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_lemma_1_3_1
-- name    : LovejoyPOMDP.Monotone.lemma_1_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:56:44.985177+00:00
-- url     : https://prove2.me/theorems/4832000f-b38e-4e49-922c-0134f2aa7cf0
-- title:
--   Lemma 1.3, part 1 — a TP₂ transition matrix preserves the MLR order: π ≥r π′ ⇒ πP^a ≥r π′P^a
-- statement:
--   Consider a finite POMDP as in §2 of the paper. Suppose that for each action $a\in A$ the transition matrix $P^a$ is $\mathrm{TP}_2$ on $S\times S$. Then for every $a\in A$ and all beliefs $\pi,\pi'\in\Pi(S)$,
--   $$\pi\ge_r\pi'\ \Longrightarrow\ \pi P^a\ge_r\pi' P^a.$$
--
--   Together with Lemma 1.2(2), this shows that the Bayes update $T(\pi,a,k)$ is MLR-nondecreasing in the prior $\pi$.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, Lemma 1.3, part 1

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 739, Lemma 1.3, part 1.

If every `P^a` is TP₂ on `S × S`, then for every `a ∈ A` and `π ≥r π'` in `Π(S)`,
`πP^a ≥r π'P^a`. -/
theorem lemma_1_3_1 {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hP : ∀ a, TP2 (M.P a)) (a : A) {π π' : S → ℝ}
    (hπ : π ∈ stdSimplex ℝ S) (hπ' : π' ∈ stdSimplex ℝ S) (h : MLRGE π π') :
    MLRGE (M.predict π a) (M.predict π' a) := by sorry

end LovejoyPOMDP.Monotone
