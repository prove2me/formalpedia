-- Prove2me | Theorems.Thm_MallowsChoice_DP_pi_sum_eq_choiceProb
-- name    : MallowsChoice.DP.pi_sum_eq_choiceProb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:19.927837+00:00
-- url     : https://prove2.me/theorems/b7c2519b-292f-4820-aad6-c229b16e699d
-- title:
--   §4.1 display, p. 17 — choice probability decomposes by final position
-- statement:
--   Let $S$ be an offer set, $a_i\in S$, and $\theta\ge0$. Write $\pi(i,s,n)$ for the probability that after Algorithm 1 has inserted all $n$ products, $a_i$ is first among those in $S$ and occupies position $s$. Then
--
--   $$
--   P(a_i\mid S)=\sum_{s=1}^{n}\pi(i,s,n).
--   $$
--
--   The identity partitions the rankings contributing to an offered product's choice probability by that product's final position.
--
--   **Formalization Note** $P$ uses the Mallows sum in equation (1), while $\pi$ uses Algorithm 1's law. Lemma 1 supplies their identification. The claim is for $a_i\in S$: equation (1)'s indicator does not itself test that $a_i$ is offered.
-- source:
--   Désir, Goyal, Jagabathula & Segev, Mallows-Smoothed Distribution over Rankings Approach for Modeling Choice, SSRN 3172997 (manuscript OPRE-2018-04-176, version of 2019-09-25; Oper. Res. doi:10.1287/opre.2020.2085), §4.1, displayed choice-probability decomposition, p. 17

import Mathlib
import Definitions.Def_MallowsChoice_DP_Setting

namespace MallowsChoice.DP

open Finset

/-- The displayed decomposition in §4.1, p. 17. -/
theorem pi_sum_eq_choiceProb (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (S : Finset (Fin n)) (a : Fin n) (ha : a ∈ S) :
    choiceProb θ S a =
      ∑ s ∈ Icc 1 n, piProb θ S (a.val + 1) s n := by sorry

end MallowsChoice.DP
