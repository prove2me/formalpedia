-- Prove2me | Theorems.Thm_GirthBethe_Sharp_auxiliary_flow_value
-- name    : GirthBethe.Sharp.auxiliary_flow_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:18:35.02024+00:00
-- url     : https://prove2.me/theorems/a665508c-1867-43ac-ba49-0f24c17f7157
-- title:
--   Lemma 4.5 — $\varphi$ is an $s$–$t$ flow on $N$ with value (4.4)
-- statement:
--   Let $G=(L\sqcup R,E)$ be a finite simple bipartite graph and let $J_e^+,J_e^-\ge0$. Choose, at every vertex, nonnegative coefficients $\alpha^v_{ef}$ for distinct incident edges satisfying (4.2). Write $J_v^\pm=\sum_{e\ni v}J_e^\pm$ and $\delta_{v,e}=J_e^+-\sum_{f\ni v,\,f\ne e}\alpha^v_{fe}$.
--
--   On the specific auxiliary network $N$ of Definition 4.4, put $J_e^+$ on the plus traversal of $e$, $J_e^-$ on its minus traversal, $\alpha^v_{ef}$ on the indexed transfer, and $\delta_{v,e}$ on the source or sink arc at $(v,e,+)$. The resulting assignment $\varphi$ is an $s$–$t$ flow, and
--   $$\operatorname{val}(\varphi)=\sum_{e\in E}(J_e^+-J_e^-)=\frac12\sum_{v\in L\sqcup R}(J_v^+-J_v^-).$$
--   This identifies the value of the constructed flow in edge and vertex coordinates, including the arbitrary nonnegative weights permitted by the p. 12 preamble.
--
--   Differences from the source:
--   - encoding: a finite simple bipartite graph G = (L ⊔ R, E) → finite types L and R and an edge finset E ⊆ L × R; vertexWeight J v = ∑_{e ∋ v} J_e; reason: each edge has exactly one endpoint in each class; no extra graph condition is introduced
--   - generalization: the weights and coefficients of §4.1, including the arbitrary-weight convention on p. 12 → arbitrary nonnegative J^± on any finite bipartite graph and any coefficient family satisfying (4.2) at every vertex, without a girth, balance or matching-law assumption; reason: the flow identities follow from the incidence structure and (4.2); every source instance supplies these data
--   - encoding: an s–t flow on N and its value → a real function on ordered node pairs, zero off arcs, nonnegative on arcs, conserved at nodes other than s and t; its value is net outflow at s; reason: the same flow and value, with the assignment constructed as in Definition 4.4
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 14, Lemma 4.5, equation (4.4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_FlowNetwork

open Finset

namespace GirthBethe.Sharp

/-- Lemma 4.5 for the arbitrary nonnegative weights of the p. 12 preamble:
for coefficients satisfying (4.2) at every vertex, the specific φ is an s–t flow with value (4.4). -/
theorem auxiliary_flow_value {L R : Type*} [Fintype L] [Fintype R]
    (E : Finset (L × R)) (Jp Jm : Edge E → ℝ)
    (hp : ∀ e, 0 ≤ Jp e) (hm : ∀ e, 0 ≤ Jm e)
    (α : L ⊕ R → Edge E → Edge E → ℝ)
    (hα : ∀ v, SatisfiesCoeffCond Jp Jm v (α v)) :
    IsSTFlow (auxNetwork E) (auxFlow Jp Jm α) ∧
      flowValue (auxNetwork E) (auxFlow Jp Jm α) =
        (∑ e : Edge E, (Jp e - Jm e)) ∧
      (∑ e : Edge E, (Jp e - Jm e)) =
        (1 / 2 : ℝ) * ∑ v : L ⊕ R, (vertexWeight Jp v - vertexWeight Jm v) := by sorry

end GirthBethe.Sharp
