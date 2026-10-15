-- Prove2me | Theorems.Thm_OAI_CompactBanach_finite_placement
-- name    : OAI.CompactBanach.finite_placement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:08:41.072995+00:00
-- url     : https://prove2.me/theorems/4476542a-8536-4e3f-afb2-89b6c0dca01e
-- title:
--   Finite pieces of the strip set embed linearly with distortion 36 into any infinite-dimensional normed space
-- statement:
--   Let $S\subseteq\ell^2$ be the strip set: the set of all points
--   $$
--   z(p,w)=p_1e_0+p_2e_1+\sum_{j:\,w_j\neq0} r_j\,e_{2+\pi(j,\,w_j-1)}
--   $$
--   for admissible pairs $(p,w)$ of a base point $p=(p_1,p_2)\in\mathbb{R}^2$ and a finitely supported tuple $w:\mathbb{N}\to\mathbb{N}$, with the metric of real $\ell^2$. Here $e_0,e_1,\dots$ are the standard unit vectors of $\ell^2$, $r_j=1000^{-(j+1)}$, and $\pi$ is a pairing bijection of $\mathbb{N}\times\mathbb{N}$ onto $\mathbb{N}$; admissibility (a colored-strip condition on $p$ at each level where $w_j\neq0$) plays no role below.
--
--   **Theorem.** Let $B$ be a real normed space that is not finite-dimensional (completeness is not assumed), and let $X\subseteq S$ be a finite set. Then there is a real-linear map $T:\ell^2\to B$ such that for all $x,y\in X$
--   $$
--   \frac{\|x-y\|}{6}\le\|Tx-Ty\|\le6\,\|x-y\| .
--   $$
--
--   In particular every finite subset of $S$ embeds into every infinite-dimensional real normed space with distortion at most $36$, through the restriction of a single linear map. Placing such finite pieces in $B$, suitably rescaled, is how the failure of $S$ to embed into finite-dimensional spaces is transferred to a compact subset of an arbitrary infinite-dimensional Banach space.
--
--   **Formalization Note** $S$ is `constructedSet`, $X$ is a `Finset RealL2` all of whose points are assumed to lie in `constructedSet`, and $T$ is a `LinearMap` (`RealL2 →ₗ[ℝ] B`); continuity of $T$ is not asserted. Distances are written with `dist`, i.e. norms of differences.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/FinitePlacement.lean#L34-L58

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

open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators
open DoublingHilbert

theorem OAI.CompactBanach.finite_placement {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (hB : ¬ FiniteDimensional ℝ B) (X : Finset RealL2)
    (hX : ∀ z ∈ X, z ∈ constructedSet) :
    ∃ T : RealL2 →ₗ[ℝ] B, ∀ x ∈ X, ∀ y ∈ X,
       dist x y / 6 ≤ dist (T x) (T y) ∧ dist (T x) (T y) ≤ 6 * dist x y := by sorry
