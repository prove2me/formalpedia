-- Prove2me | Theorems.Thm_MetricTSPSublinear_rootedMSF_candidate
-- name    : MetricTSPSublinear.rootedMSF_candidate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:29:01.26115+00:00
-- url     : https://prove2.me/theorems/a1e2bd74-8771-477b-bb83-32a50d77f06d
-- title:
--   Rooted MSF edges are candidate edges (Claim 9.3)
-- statement:
--   Let $d$ be a metric on $V$, $R\subseteq V$ a set of roots, $F$ a rooted minimum spanning forest for $R$, and $S_0\subseteq R$. Then every edge $uv$ of $F$ is a **candidate edge** with respect to $S_0$:
--   $$d(u,v)\le d(u,S_0)\qquad\text{or}\qquad d(u,v)\le d(v,S_0),$$
--   where $d(x,S_0)=\min_{s\in S_0}d(x,s)$ (the condition is vacuous when $S_0=\emptyset$).
--
--   In the paper $S_0$ is a random sample of the roots; with high probability every vertex has only $\tilde O(n^{a_0})$ candidate edges, so the children of a vertex in $F_{\mathrm{root}}$ can be found among its candidate edges with few queries (Claim 9.3).
--
--   **Formalization Note** The two alternatives are stated with a universal quantifier over $S_0$, which is equivalent to the inequality with $d(\cdot,S_0)$ for nonempty $S_0$.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §9.1, Claim 9.3 and its proof, pp.35–36 (PDF pp.37–38).

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_edgeCost
import Definitions.Def_MetricTSPSublinear_treeDist
import Definitions.Def_MetricTSPSublinear_IsRootedMSF

namespace MetricTSPSublinear

/-- **Candidate edges contain the rooted MSF.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two
Approximation*, arXiv:2611.04283, §9.1, p.34–36 (PDF p.36–38): "an edge (u, v) is a candidate if d(u, v) ≤ d(u, S0)
or d(u, v) ≤ d(v, S0)" and, in the proof of Claim 9.3, "The candidate edges include the edges of Froot". For a rooted
MSF `F` for roots `R ⊇ S0`, every edge `s(u, v) ∈ F` satisfies `d(u,v) ≤ d(u,s)` for all `s ∈ S0`, or
`d(u,v) ≤ d(v,s)` for all `s ∈ S0`. -/
theorem rootedMSF_candidate {n : ℕ} {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d)
    {R : Finset (Fin n)} {F : Finset (Sym2 (Fin n))} (hF : IsRootedMSF d R F) {S0 : Finset (Fin n)}
    (hS0 : S0 ⊆ R) {u v : Fin n} (he : s(u, v) ∈ F) :
    (∀ s ∈ S0, d u v ≤ d u s) ∨ (∀ s ∈ S0, d u v ≤ d v s) := by sorry

end MetricTSPSublinear
