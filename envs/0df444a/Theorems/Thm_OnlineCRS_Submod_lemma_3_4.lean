-- Prove2me | Theorems.Thm_OnlineCRS_Submod_lemma_3_4
-- name    : OnlineCRS.Submod.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:07.890266+00:00
-- url     : https://prove2.me/theorems/cb7ec1d7-10bd-408b-acd4-c33fcd6c2aed
-- title:
--   Lemma 3.4, p. 17 — the characteristic CRS of a (b, c)-selectable greedy OCRS is (b, c)-balanced and monotone
-- statement:
--   Let $b,c\in[0,1]$, let $\mathcal F$ be a down-closed feasible family with a relaxation $P\subseteq[0,1]^N$, and let $\pi$ be a $(b,c)$-selectable (randomized) greedy OCRS for $P$. Then its characteristic CRS $\bar\pi$ is
--
--   1. $(b,c)$-balanced: for every $x\in bP$ and every $e$ with $x_e>0$, $\Pr[e\in\bar\pi(R(x))\mid e\in R(x)]\ge c$;
--   2. monotone: for every input $x$, $\Pr[e\in\bar\pi(S_1)]\ge\Pr[e\in\bar\pi(S_2)]$ whenever $e\in S_1\subseteq S_2$.
--
--   The lemma translates selectability, an online notion, into the two properties of offline contention resolution schemes under which the rounding result of Chekuri, Vondrák and Zenklusen (Lemma 3.5) applies.
--
--   **Formalization Note** Balancedness is the corrected Definition 3.1 ("$\ge c$", not "$\ge c\cdot x_e$"), written as $\Pr[e\in\bar\pi(R(x)),\,e\in R(x)]\ge c\,x_e$.
-- source:
--   arXiv:1508.00142v2, Lemma 3.4, p. 17

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Submod_Model
import Definitions.Def_OnlineCRS_Submod_CRS

namespace OnlineCRS.Submod

/-- Lemma 3.4 (arXiv:1508.00142v2, p. 17): the characteristic CRS `π̄` of a `(b, c)`-selectable greedy OCRS
`π` is `(b, c)`-balanced and monotone. -/
theorem lemma_3_4 {α : Type} [Fintype α] [DecidableEq α] (𝓕 : Finset α → Prop)
    (P : Set (α → ℝ)) (hPoly : IsPolytope P) (hRel : IsRelaxation 𝓕 P)
    (b c : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (w : (α → ℝ) → Finset (Finset α) → ℝ) (hw : OnlineCRS.Matroid.IsSelectableRand 𝓕 P b c w) :
    IsBalanced P b c (charCRS w) ∧ IsMonotoneCRS (charCRS w) := by sorry

end OnlineCRS.Submod
