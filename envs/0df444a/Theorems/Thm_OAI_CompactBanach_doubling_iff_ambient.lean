-- Prove2me | Theorems.Thm_OAI_CompactBanach_doubling_iff_ambient
-- name    : OAI.CompactBanach.doubling_iff_ambient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:10:32.164418+00:00
-- url     : https://prove2.me/theorems/04bed3b4-4fc8-46c5-95ec-809ad7e7f408
-- title:
--   Subspace and ambient formulations of the doubling condition are equivalent
-- statement:
--   Let $(B,d)$ be a metric space, $K\subseteq B$ a subset and $\Lambda\in\mathbb{N}$. Consider the following two conditions.
--
--   1. **Doubling at most $\Lambda$ (subspace form).** For every $x\in K$ and every $r>0$ there is a finite set $C$ of points of the metric subspace $K$ with $|C|\le\Lambda$ such that every $y\in K$ with $d(y,x)<r$ satisfies $d(y,c)<r/2$ for some $c\in C$.
--   2. **Ambient doubling with constant $\Lambda$.** For every $x\in K$ and every $r>0$ there is a finite set $C\subseteq B$ with $C\subseteq K$ and $|C|\le\Lambda$ such that every $y\in K$ with $d(y,x)<r$ satisfies $d(y,c)<r/2$ for some $c\in C$.
--
--   **Theorem.** These conditions are equivalent:
--   $$
--   K\ \text{is doubling at most }\Lambda\quad\Longleftrightarrow\quad K\ \text{satisfies ambient doubling with constant }\Lambda .
--   $$
--
--   Mathematically both conditions say that $K$ is doubling with constant $\Lambda$ and centers in $K$; the content of the theorem is that a finite set of centers can be moved between the subspace $K$ and the ambient space $B$ without increasing its size. It lets covers be constructed with centers in the ambient space and then be read back in the subspace form used in the main statement.
--
--   **Formalization Note** The subspace form is `DoublingAtMost K bound` from the mission's definitions: centers form a `Finset K`, points are elements of the subtype, and the radius is written `r / ((2 : ℕ) : ℝ)`. The ambient form is `AmbientDoubling K bound`, whose centers form a `Finset B` with all members in `K`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/IntrinsicCovers.lean#L16-L37

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

theorem OAI.CompactBanach.doubling_iff_ambient {B : Type*} [MetricSpace B] {K : Set B} {bound : ℕ} :
    DoublingAtMost K bound ↔ AmbientDoubling K bound := by sorry
