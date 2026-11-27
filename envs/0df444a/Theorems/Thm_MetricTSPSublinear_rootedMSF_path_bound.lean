-- Prove2me | Theorems.Thm_MetricTSPSublinear_rootedMSF_path_bound
-- name    : MetricTSPSublinear.rootedMSF_path_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:29:06.436262+00:00
-- url     : https://prove2.me/theorems/666f24b3-f9e2-4298-a7ce-81de31d62987
-- title:
--   Rooted MSF path edges weigh at most $d(v,S_{\mathrm{root}})$
-- statement:
--   Let $d$ be a metric on $V$, $R\subseteq V$ a set of roots and $F$ a rooted minimum spanning forest for $R$. Let $v\in V$, let $r\in R$ be the root of the component of $v$, and let $e$ be an edge on the path from $v$ to $r$ in $F$. Then
--   $$w(e)\le d(v,x)\qquad\text{for every root }x\in R,$$
--   that is, $w(e)\le d(v,R)$.
--
--   In the paper this shows that $b_v=d(v,S_{\mathrm{root}})$ is an upper bound on the contribution $f_v$ of $v$ to the fragment weight $A$, which makes importance sampling of $A$ possible.
--
--   **Formalization Note** "The path from $v$ to $r$" is the set `pathEdges F v r` of edges of $F$ whose removal disconnects $v$ from $r$.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §9.2.1, proof of Claim 9.5, p.37 (PDF p.39).

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_edgeCost
import Definitions.Def_MetricTSPSublinear_treeDist
import Definitions.Def_MetricTSPSublinear_IsRootedMSF

namespace MetricTSPSublinear

/-- **Edges on the path to the root are short.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two
Approximation*, arXiv:2611.04283, §9.2.1, proof of Claim 9.5, p.37 (PDF p.39): "f_v ≤ w_T(e_v) ≤ d(v, Sroot) …
the second inequality can be proven by considering Kruskal's algorithm: … any edge on the path from v to its fragment
root has a weight of at most d(v, Sroot)." In a rooted MSF `F` for the roots `R`, every edge on the path from `v` to
its root `r` weighs at most `d(v, x)` for every root `x`. -/
theorem rootedMSF_path_bound {n : ℕ} {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d)
    {R : Finset (Fin n)} {F : Finset (Sym2 (Fin n))} (hF : IsRootedMSF d R F) {v r : Fin n}
    (hr : r ∈ R) (hvr : reachIn F v r) {x : Fin n} (hx : x ∈ R) {e : Sym2 (Fin n)}
    (he : e ∈ pathEdges F v r) : DoublingMST.edgeCost d e ≤ d v x := by sorry

end MetricTSPSublinear
