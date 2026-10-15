-- Prove2me | Theorems.Thm_OAI_CompactBanach_ambient_iterated_cover
-- name    : OAI.CompactBanach.ambient_iterated_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:11:48.808196+00:00
-- url     : https://prove2.me/theorems/289c87fa-7d32-45bc-a487-43f0276b6a84
-- title:
--   Iterated doubling: $L^n$ centers cover a ball at radius $r/2^n$
-- statement:
--   Let $(B,d)$ be a metric space and let $K\subseteq B$ satisfy the ambient doubling condition with constant $L\in\mathbb{N}$: for every $x\in K$ and $r>0$ there is a finite set of at most $L$ centers in $K$ such that every point of $K$ at distance less than $r$ from $x$ is at distance less than $r/2$ from one of them.
--
--   **Theorem.** Let $n\in\mathbb{N}$, $x\in K$ and $r>0$. Then there is a finite set $C\subseteq K$ with $|C|\le L^n$ such that
--   $$
--   \forall y\in K:\qquad d(y,x)<r\ \Longrightarrow\ \exists c\in C:\ d(y,c)<\frac{r}{2^n} .
--   $$
--
--   This is the iteration of the doubling condition: the part of $K$ in a ball of radius $r$ is covered by $L^n$ balls of radius $r/2^n$ centered in $K$. It is used to cover the part of a cluster in a ball by $L^2$ balls of a quarter of the radius, and to transfer doubling bounds through maps of bounded distortion, where $L^8$ balls of radius $r/2^8$ are needed.
--
--   **Formalization Note** The hypothesis is `AmbientDoubling K L` and the centers form a `Finset B` all of whose members lie in `K`. For $n=0$ the bound is $L^0=1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/IntrinsicCovers.lean#L40-L71

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

open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators

theorem OAI.CompactBanach.ambient_iterated_cover {B : Type*} [MetricSpace B] {K : Set B} {L : ℕ}
    (h : AmbientDoubling K L) (n : ℕ) {x : B} (hx : x ∈ K) {r : ℝ} (hr : 0 < r) :
    ∃ centers : Finset B, (∀ c ∈ centers, c ∈ K) ∧ centers.card ≤ L ^ n ∧
      ∀ y ∈ K, dist y x < r → ∃ c ∈ centers, dist y c < r / (2 : ℝ) ^ n := by sorry
