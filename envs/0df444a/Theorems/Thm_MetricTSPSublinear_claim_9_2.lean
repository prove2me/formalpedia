-- Prove2me | Theorems.Thm_MetricTSPSublinear_claim_9_2
-- name    : MetricTSPSublinear.claim_9_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T05:08:46.364803+00:00
-- url     : https://prove2.me/theorems/cbf05fca-b4b9-56d0-86be-9a5f38a13d46
-- title:
--   Claim 9.2: Prim from $v$ finds the path to its root in $F_{\mathrm{root}}$
-- statement:
--   Let $d$ be a metric on $V$, $R\subseteq V$ a nonempty set of roots, and $F=F_{\mathrm{root}}$ the rooted minimum spanning forest obtained by Kruskal's algorithm with ties broken by a fixed numbering of the pairs. For a vertex $v$, run Prim's algorithm from $\{v\}$ (always adding the minimum-key pair leaving the current set) until a root is reached, and let $x$ be the root reached. Then
--
--   1. $F$ is a rooted minimum spanning forest for $R$;
--   2. $x\in R$, and $x$ is the root of the component of $v$ in $F$;
--   3. every edge added by Prim's exploration is an edge of $F$;
--   4. every edge of the $F$-path from $v$ to $x$ is added by the exploration.
--
--   So the path from $v$ to its root in $F_{\mathrm{root}}$ can be computed by a local Prim exploration that never needs the whole forest; each step costs one row query.
--
--   **Formalization Note** The theorem is stated for every vertex $v$; if $v\in R$, the exploration adds nothing and $x=v$.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §9.1, Claim 9.2 and its proof, p.35 (PDF p.37).

import Mathlib
import Definitions.Def_MetricTSPSublinear_IsRootedMSF
import Definitions.Def_MetricTSPSublinear_treeDist
import Definitions.Def_MetricTSPSublinear_rootedKruskal

namespace MetricTSPSublinear

/-- **Claim 9.2.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283,
§9.1, p.35 (PDF p.37): "Given a vertex v ∉ Sroot, let x be the root of the subtree in Froot containing v. The path from
v to x can be computed … we run Prim's algorithm starting with {v} and continue until a vertex of Sroot is reached …
Up to the point where a vertex of Sroot is reached, this is equivalent to the process described above."

With `F = kruskalRooted d R` (the tie-broken rooted MSF): `F` is a rooted MSF; Prim's exploration from `v` stops at a
root `primRoot d R v`, which is the root of `v`'s component; every edge it adds is an edge of `F`; and the whole
`F`-path from `v` to its root is among the added edges. -/
theorem claim_9_2 {n : ℕ} (d : Fin n → Fin n → ℝ) (R : Finset (Fin n)) (hR : R.Nonempty) (v : Fin n) :
    IsRootedMSF d R (RootedKruskal.kruskalRooted d R) ∧
    RootedKruskal.primRoot d R v ∈ R ∧
    reachIn (RootedKruskal.kruskalRooted d R) v (RootedKruskal.primRoot d R v) ∧
    (∀ e ∈ RootedKruskal.primPath d R v, e ∈ RootedKruskal.kruskalRooted d R) ∧
    pathEdges (RootedKruskal.kruskalRooted d R) v (RootedKruskal.primRoot d R v) ⊆
      (RootedKruskal.primPath d R v).toFinset := by sorry

end MetricTSPSublinear
