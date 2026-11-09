-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_mst_bottleneck
-- name    : MSTCuts2027.Parallel.mst_bottleneck
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:32.247977+00:00
-- url     : https://prove2.me/theorems/c294297c-538a-4e99-a53b-fda988ad937b
-- title:
--   Theorem 1 — the mincut value is the bottleneck capacity on any MST of $G_1$
-- statement:
--   Let $F$ be a symmetric real cut function on a finite vertex set $V$, and let $T$ be any maximum spanning tree of $G_1$. For distinct $u,v$ with $(u,v)$-path $p$ in $T$,
--   $$\lambda_1(u,v)=\min_{e\in p}\ \mathrm{cap}(e).$$
--   Thus an MST of $G_1$ records all the mincut values, for arbitrary $F$.
--
--   Differences from the source:
--   - encoding: any pair of vertices (u, v) → distinct u, v; reason: λ₁ is defined only for a pair that a cut can separate
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Theorem 1, printed p. 2, PDF p. 4

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel

namespace MSTCuts2027.Parallel

open FlowsNetworks.MultiTerminal

/-- Theorem 1: on any maximum spanning tree `T` of `G₁`, the mincut value of a pair is the least
capacity on the tree path between them. -/
theorem mst_bottleneck {V : Type} [Fintype V] [DecidableEq V]
    (F : Finset V → ℝ) (hF : IsSymmetricCutFunction F)
    (T : SimpleGraph V) (hT : IsMaximalSpanningSubtree ⊤ T (capacity F))
    (u v : V) (huv : u ≠ v) (p : T.Walk u v) (hp : p.IsPath) :
    IsLeast (capacity F '' {e | e ∈ p.edges}) (lam F u v) := by sorry

end MSTCuts2027.Parallel
