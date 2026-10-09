-- Prove2me | Theorems.Thm_OnlineCRS_Matching_selectability_event
-- name    : OnlineCRS.Matching.selectability_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:12.646242+00:00
-- url     : https://prove2.me/theorems/6eb757cf-b673-4307-a93c-c18c298c8f3d
-- title:
--   Proof of Theorem 2.7, p. 13 — g′ is selectable iff g′ ∈ K and A ∩ K ∩ (δ(u) ∪ δ(v) ∖ {g′}) = ∅
-- statement:
--   Let $G=(V,E)$ be a finite loopless graph, let $K,A\subseteq E$, and let $g'\in E$ be an edge with ends $u$ and $v$. Let $\mathcal F_K$ be the family of matchings contained in $K$. Then $g'$ is selectable for the active set $A$ and the family $\mathcal F_K$ (that is, $I\cup\{g'\}\in\mathcal F_K$ for every $I\subseteq A$ with $I\in\mathcal F_K$) if and only if
--
--   $$g'\in K\quad\text{and}\quad A\cap K\cap\big((\delta(u)\cup\delta(v))\setminus\{g'\}\big)=\varnothing.$$
--
--   This is the reduction behind the "Formally, we need to prove" of the paper: selectability of $g'$ is exactly the event whose probability is then bounded below by $e^{-2b}$.
-- source:
--   arXiv:1508.00142v2, proof of Theorem 2.7, p. 13, second paragraph

import Mathlib
import Definitions.Def_OnlineCRS_Matching_Model

namespace OnlineCRS.Matching

/-- Proof of Theorem 2.7, p. 13: selectability for the sampled matching family. -/
theorem selectability_event {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (K A : Finset E) (g : E) (u v : V)
    (hg : G.ends g = s(u, v)) :
    OnlineCRS.Matroid.Selectable (famK G K) A g ↔
      g ∈ K ∧ A ∩ K ∩ otherIncident G u v g = ∅ := by sorry

end OnlineCRS.Matching
