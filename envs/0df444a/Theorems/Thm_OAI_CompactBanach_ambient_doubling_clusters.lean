-- Prove2me | Theorems.Thm_OAI_CompactBanach_ambient_doubling_clusters
-- name    : OAI.CompactBanach.ambient_doubling_clusters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:15:27.774916+00:00
-- url     : https://prove2.me/theorems/c6affc79-fb1e-4955-b695-4358dba47310
-- title:
--   Doubling clusters placed near $2^{-(j+1)}v$ on a ray form a doubling set with constant $1+5L^2$
-- statement:
--   Let $B$ be a real normed space and $v\in B$ a unit vector, $\|v\|=1$. For $j\in\mathbb{N}$ put $\sigma_j=2^{-(j+1)}$. Let $(C_j)_{j\in\mathbb{N}}$ be finite subsets of $B$ such that
--
--   - each cluster is localized near the point $\sigma_jv$: $\|z-\sigma_jv\|\le\sigma_j/100$ for every $j$ and every $z\in C_j$;
--   - each cluster satisfies the ambient doubling condition with one common constant $L\in\mathbb{N}$: for every $j$, every $x\in C_j$ and every $r>0$ there are at most $L$ centers in $C_j$ such that every point of $C_j$ at distance less than $r$ from $x$ is at distance less than $r/2$ from one of them.
--
--   **Theorem.** The set $K=\{0\}\cup\bigcup_{j\in\mathbb{N}}C_j$ satisfies the ambient doubling condition with constant $1+5L^2$: for every $x\in K$ and every $r>0$ there is a finite set $C\subseteq K$ with
--   $$
--   |C|\le1+5L^2\qquad\text{and}\qquad\forall y\in K:\ \|y-x\|<r\ \Longrightarrow\ \exists c\in C:\ \|y-c\|<\frac r2 .
--   $$
--
--   The constant depends only on $L$, not on the clusters or on the space $B$. This is the doubling half of the construction of a compact doubling set inside an arbitrary infinite-dimensional normed space: uniformly doubling finite pieces, placed at geometrically decreasing distances along a ray, assemble into a single doubling set.
--
--   **Formalization Note** The scale $\sigma_j$ is `clusterScale j`, the clusters are `C j : Finset B`, and both the hypothesis on each cluster and the conclusion are stated with `AmbientDoubling` (centers in the ambient space, required to lie in the set).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/ClusterCover.lean#L15-L107

import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap
import Definitions.Def_OAI_Geometry_DoublingHilbert_IntrinsicCovers
import Definitions.Def_OAI_Geometry_DoublingHilbert_ClusterScales

open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators
open Filter
open scoped Topology

theorem OAI.CompactBanach.ambient_doubling_clusters
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (C : ℕ → Finset B) {v : B} (hv : ‖v‖ = 1)
    (hloc : ∀ j z, z ∈ C j → dist z (clusterScale j • v) ≤ clusterScale j / 100)
    {L : ℕ} (hC : ∀ j, AmbientDoubling (C j : Set B) L) :
    AmbientDoubling ({0} ∪ ⋃ j : ℕ, (C j : Set B)) (1 + 5 * L ^ 2) := by sorry
