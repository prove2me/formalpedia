-- Prove2me | Theorems.Thm_OnlineCRS_Matroid_corollary_2_5
-- name    : OnlineCRS.Matroid.corollary_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:23:54.496435+00:00
-- url     : https://prove2.me/theorems/9e33ab83-06b5-404b-a418-22999f09d16c
-- title:
--   Corollary 2.5 — the first chain set is proper
-- statement:
--   Let $M$ be a loopless matroid on a finite, nonempty ground set $N$, let $b\in[0,1]$, and let $x\in b\cdot P_{\mathcal B}$, where $P_{\mathcal B}=\{x\in P_{\mathcal F} : x(N)=\operatorname{rank}(N)\}$ is the base polytope. Let $S=S_{|N|}$ be the set produced from $x$ and $b$ by the refinement procedure ($S_0=\varnothing$, $S_i=\{e : \Pr[e\in\operatorname{span}((R(x)\cup S_{i-1})\setminus\{e\})]>b\}$). Then
--
--   $$N_1=S\subsetneq N.$$
--
--   This shows that each refinement step of the chain construction makes progress, so that the chain $\varnothing=N_\ell\subsetneq\cdots\subsetneq N_0=N$ is reached after finitely many steps.
--
--   **Formalization Note** The ground set is the whole finite type, assumed nonempty. The assumption $x\in b\cdot P_{\mathcal B}$ is the standing assumption of §2.1.1 stated just before Lemma 2.4. Looplessness is added: for a single loop $e$ and $b<1$ one gets $S=\{e\}=N$, so the printed statement fails for matroids with loops.
-- source:
--   arXiv:1508.00142v2, Corollary 2.5, p. 11

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Construction

open scoped Pointwise

namespace OnlineCRS.Matroid

/-- arXiv:1508.00142v2, Corollary 2.5, p. 11. -/
theorem corollary_2_5 {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (M : Matroid α) (hE : M.E = Set.univ) [M.Loopless]
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (x : α → ℝ) (hx : x ∈ b • basePolytope M) :
    Sfin M x b ≠ Finset.univ := by sorry

end OnlineCRS.Matroid
