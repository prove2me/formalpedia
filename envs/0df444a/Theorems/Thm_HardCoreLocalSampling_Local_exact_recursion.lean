-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_exact_recursion
-- name    : HardCoreLocalSampling.Local.exact_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:30.86456+00:00
-- url     : https://prove2.me/theorems/340c5b8b-6874-4990-b519-a45592f28370
-- title:
--   Lemma 6 — Exact recursion and child degree bound
-- statement:
--   Fix an integer $\Delta\ge3$ and a positive rational $\lambda<\lambda_c(\Delta)$. Let $G$ be a finite simple graph with ordered vertex labels and maximum degree at most $\Delta$, let $H=G-D$ be an induced subgraph, let $v\in V(H)$, and list its neighbors in $H$ in increasing label order as $u_1,\ldots,u_d$. Put $H_i=H-\{v,u_1,\ldots,u_{i-1}\}$. Writing $R_H(u)$ for the occupied probability divided by the unoccupied probability in the unpinned hard-core model on $H$,
--
--   $$
--   R_H(v)=\lambda\prod_{i=1}^d\frac1{1+R_{H_i}(u_i)}.
--   $$
--
--   Every child root $u_i$ has degree at most $\Delta-1$ in $H_i$. An isolated root has $d=0$, empty product one, and odds $\lambda$.
--
--   This is the exact finite-graph identity underlying the message recursion; it assumes no approximation, bounded growth, girth, connectedness, or bipartiteness.
--
--   Differences from the source:
--   - encoding: the induced graph H and its children H_i → the graph G with the deleted vertices pinned unoccupied in the weight sums; reason: independent sets of an induced deletion graph correspond exactly to independent sets of the original graph avoiding the deleted vertices
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 6, equation (1), printed p.5 (PDF p.6); standing assumptions §2, printed p.2 (PDF p.3)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Deletion

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 6, printed p.5 (PDF p.6).
Both the exact ratio identity (1) and the child degree bound are included, for every induced
graph `H = G - D` and vertex `v ∈ H`. The fixed degree and fugacity assumptions are from §2. -/
theorem exact_recursion {V : Type*} [Fintype V] [LinearOrder V] {Delta : ℕ}
    (G : SimpleGraph V) (lam : ℚ)
    (hDelta : 3 ≤ Delta) (hlam : 0 < lam) (hunique : lam < criticalFugacity Delta)
    (hdegree : MaxDegreeLE G Delta) (D : Finset V) (v : V) (hv : v ∉ D) :
    deletionOdds G (lam : ℝ) D v =
      (lam : ℝ) * ∏ i : Fin (orderedNeighbors G D v).length,
        (1 + deletionOdds G (lam : ℝ) (childDeleted G D v i)
          ((orderedNeighbors G D v)[i.val]))⁻¹ ∧
    ∀ i : Fin (orderedNeighbors G D v).length,
      residualDegree G (childDeleted G D v i) ((orderedNeighbors G D v)[i.val]) ≤
        Delta - 1 := by sorry

end HardCoreLocalSampling.Local
