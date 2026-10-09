-- Prove2me | Theorems.Thm_OnlineCRS_Submod_observation_3_3
-- name    : OnlineCRS.Submod.observation_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:30.889674+00:00
-- url     : https://prove2.me/theorems/d07cce7c-a2d4-48b9-adca-c70bd90cb9ad
-- title:
--   Observation 3.3, p. 16 — π̄(A) is always contained in the set selected by the greedy OCRS
-- statement:
--   Let $\mathcal F_x$ be a greedy family for a feasible family $\mathcal F$ (down-closed, containing $\emptyset$, contained in $\mathcal F$), let $A\subseteq N$ be the set of active elements, and let $\sigma$ be any arrival order of $N$. Let $\bar\pi(A)=\{e\in A\mid I\cup\{e\}\in\mathcal F_x\ \forall I\subseteq A,\ I\in\mathcal F_x\}$ and let $S_\sigma(A)$ be the set selected by the greedy OCRS when the elements arrive in the order $\sigma$. Then
--   $$\bar\pi(A)\subseteq S_\sigma(A).$$
--
--   Because the inclusion holds for every order, it holds in particular for the order chosen by the almighty adversary, which knows $A$ and $\mathcal F_x$. This is what lets the analysis of Theorem 1.10 replace the online selection by the offline characteristic CRS.
-- source:
--   arXiv:1508.00142v2, Observation 3.3, p. 16

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Submod_Model
import Definitions.Def_OnlineCRS_Submod_CRS

namespace OnlineCRS.Submod

/-- Observation 3.3 (arXiv:1508.00142v2, p. 16): for every greedy family `F_x = Fam`, every active set `A`
and every order `σ` of `N` (in particular one chosen by the almighty adversary), the set `π̄(A)` is a
subset of the elements selected by the greedy OCRS. -/
theorem observation_3_3 {α : Type} [Fintype α] [DecidableEq α] (𝓕 : Finset α → Prop)
    (Fam : Finset (Finset α)) (hFam : OnlineCRS.Matroid.IsGreedyFamily 𝓕 Fam) (A : Finset α) (σ : List α)
    (hσ : IsOrder σ) :
    charMap Fam A ⊆ greedyRun Fam A σ := by sorry

end OnlineCRS.Submod
