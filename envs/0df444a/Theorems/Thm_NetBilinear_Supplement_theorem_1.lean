-- Prove2me | Theorems.Thm_NetBilinear_Supplement_theorem_1
-- name    : NetBilinear.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:42:38.363517+00:00
-- url     : https://prove2.me/theorems/685a6b05-9874-47ca-aa96-ae49b53e0fc0
-- title:
--   Theorem 1 — the constraints of $\Xi$ and $\Delta_m$ with all class-$l^\pm$ EC&R inequalities describe $\operatorname{conv}(\mathcal S)$
-- statement:
--   Let $\mathcal S=\{(x;y;z)\in\Xi\times\Delta_m\times\mathbb R^\kappa : y^\top A^kx=z_k,\ k\in K\}$, where $\Xi=\{x : Ex\ge f,\ 0\le x\le u\}$, $\Delta_m=\{y\ge 0 : \mathbf 1^\top y\le 1\}$, and every $A^k$ has exactly one entry equal to $1$. Then
--   $$
--   \operatorname{conv}(\mathcal S)=\{(x;y;z) : x\in\Xi,\ y\in\Delta_m,\ (x,y,z)\text{ satisfies every class-}l^\pm\text{ EC\&R inequality, for every }l\in K\}.
--   $$
--   That is, the linear constraints of $\Xi$ and $\Delta_m$, together with all class-$l^\pm$ EC&R inequalities for all $l\in K$, give a convex hull description of $\mathcal S$.
--
--   The paper states this result as the core of the EC&R procedure and attributes it to Theorem 2.7 of its reference [11]. It is not proved in the paper.
--
--   Differences from the source:
--   - reading: "a convex hull description of S can be obtained by the linear constraints in Ξ and ∆m together will all class-l± EC&R inequalities" → conv(S) equals the set of points of Ξ × ∆m × ℝ^κ satisfying every class-l± EC&R inequality; reason: a description of a set by inequalities means the set is their solution set ("will" is a misprint for "with").
--   - encoding: A^k with all entries zero except one equal to one → the position pos k = (i, j) of that entry; reason: the matrix is determined by it, same instances.
--   - encoding: the linear inequality obtained by aggregating and then relaxing the remaining bilinear terms → aggValue + relaxValue ≥ 0, with a relaxation choice recorded for every pair (j, i); reason: the bilinear terms cancel identically in this sum, so it is the same linear inequality, and the choice is used only where the aggregated coefficient is nonzero.
--   - generalization: N = {1,…,n}, M = {1,…,m}, K = {1,…,κ}, T = {1,…,τ} → arbitrary finite types, possibly empty; reason: nonempty types are the source's instances. An empty N or M forces K = ∅, so S = Ξ × ∆m × ℝ⁰ is convex and there are no EC&R inequalities.
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, Theorem 1, p.3 (attributed to Theorem 2.7 of [11]); set S, p.2; EC&R procedure and relaxation step, p.3

import Mathlib
import Definitions.Def_NetBilinear_Supplement_BilinearSet
import Definitions.Def_NetBilinear_Supplement_ECRInequality

namespace NetBilinear.Supplement

/-- **Theorem 1: the linear constraints of `Ξ` and `Δ_m` together with all class-`l±` EC&R
inequalities for all `l ∈ K` describe `conv(S)`.**
Khademnia & Davarnia, *Convexification of Bilinear Terms over Network Polytopes*,
arXiv:2302.14151v2, Theorem 1, p.3 (attributed there to Theorem 2.7 of [11]): "A convex hull
description of S can be obtained by the linear constraints in Ξ and ∆m together will all
class-l± EC&R inequalities for all l ∈ K."

For finite `N`, `M`, `K` and rows `T`, and any data `E, f, u, (A^k)_k` of the set `S` (p.2),
the convex hull of `S` equals the set of points `(x, y, z)` with `x ∈ Ξ`, `y ∈ Δ_m` that satisfy
every class-`l±` EC&R inequality (`ECRInequality.Holds`), for every `l ∈ K` and both signs.

**Formalization Note.** "A convex hull description … can be obtained by" is read as equality
of `conv(S)` with the set these inequalities define. Every EC&R inequality is valid on `S`, so
`⊆` is the routine half; `⊇` is the content of the theorem. -/
theorem theorem_1 {N M K R : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]
    [Fintype K] [Fintype R] (S : BilinearSet N M K R) :
    convexHull ℝ S.carrier = {p | S.InXiDelta p ∧ ∀ e : ECRInequality S, e.Holds p} := by sorry

end NetBilinear.Supplement
