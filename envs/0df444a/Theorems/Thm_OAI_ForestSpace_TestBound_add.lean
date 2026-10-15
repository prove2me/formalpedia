-- Prove2me | Theorems.Thm_OAI_ForestSpace_TestBound_add
-- name    : OAI.ForestSpace.TestBound.add
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:11:56.556723+00:00
-- url     : https://prove2.me/theorems/560be799-45d7-4ee9-9b10-a8556443d4a9
-- title:
--   Triangle inequality for disjoint-segment test bounds
-- statement:
--   A *segment* of a partially ordered set $V$ is a finite set $S\subseteq V$ that is a chain (any two of its elements are comparable) and is order-convex ($a,b\in S$ and $a\le c\le b$ imply $c\in S$); the empty set is a segment. For $u:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $u(S)=\sum_{v\in S}u(v)$, and let
--   $$
--   \|u\|_{\mathrm{seg}}^2=\sup\Bigl\{\sum_{i\in I}u(S_i)^2\ :\ (S_i)_{i\in I}\ \text{a finite family of pairwise disjoint segments}\Bigr\}\in[0,\infty].
--   $$
--   Thus $\|u\|_{\mathrm{seg}}^2\le C$ means that $\sum_{i\in I}u(S_i)^2\le C$ for every finite family of pairwise disjoint segments; for finitely supported $u$, $\|u\|_{\mathrm{seg}}$ is the disjoint-segment norm.
--
--   **Theorem.** Let $V$ be a partially ordered set, let $u,v:V\to\mathbb{R}$ be arbitrary functions and let $A,B\ge0$. If $\|u\|_{\mathrm{seg}}^2\le A^2$ and $\|v\|_{\mathrm{seg}}^2\le B^2$, then $\|u+v\|_{\mathrm{seg}}^2\le(A+B)^2$; that is, for every finite family $(S_i)_{i\in I}$ of pairwise disjoint segments,
--   $$
--   \sum_{i\in I}\bigl(u(S_i)+v(S_i)\bigr)^2\le(A+B)^2 .
--   $$
--
--   This is the triangle inequality behind the disjoint-segment norm: bounds for two functions combine into a bound for their sum. In the paired-correction estimate it shows that a gate correction plus a multiple $\tau k$ with $|\tau|\le1$ has squared segment norm at most $4$.
--
--   **Formalization Note** The hypothesis $\|u\|_{\mathrm{seg}}^2\le C$ is the proposition `TestBound u C`, which quantifies over all finite index types and all families of pairwise disjoint segments indexed by them. No finiteness of the supports of $u$ and $v$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Segments.lean#L89-L113

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [PartialOrder V]

theorem OAI.ForestSpace.TestBound.add {u v : V → ℝ} {A B : ℝ}
    (hu : TestBound u (A ^ 2)) (hv : TestBound v (B ^ 2))
    (hA : 0 ≤ A) (hB : 0 ≤ B) : TestBound (u + v) ((A + B) ^ 2) := by sorry
