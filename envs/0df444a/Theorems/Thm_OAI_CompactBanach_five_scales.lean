-- Prove2me | Theorems.Thm_OAI_CompactBanach_five_scales
-- name    : OAI.CompactBanach.five_scales
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:14:08.020639+00:00
-- url     : https://prove2.me/theorems/9784e952-fcc6-4059-8600-f084dc779de9
-- title:
--   At most five dyadic scales fit in the window $(r/4,\ \tfrac{400}{97}r]$
-- statement:
--   For $j\in\mathbb{N}$ let $\sigma_j=2^{-(j+1)}$ be the dyadic cluster scale.
--
--   **Theorem.** Let $r>0$ and let $s\subseteq\mathbb{N}$ be a finite set of indices such that
--   $$
--   \frac r4<\sigma_j\le\frac{400}{97}\,r\qquad\text{for every } j\in s .
--   $$
--   Then $s$ has at most $5$ elements.
--
--   The ratio of the endpoints of the window is $\frac{1600}{97}<32=2^5$, so the window contains at most five consecutive powers of $2$. In the doubling estimate for a union of clusters placed at the scales $\sigma_j$, this bounds the number of clusters that can meet a ball of radius $r$ while being too far from the origin to be absorbed by a single center at $0$.
--
--   **Formalization Note** The scale is `clusterScale j = (1 / 2 : ℝ) ^ (j + 1)`, $s$ is a `Finset ℕ`, and the conclusion is `s.card ≤ 5`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/ClusterScales.lean#L70-L93

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

theorem OAI.CompactBanach.five_scales {r : ℝ} (hr : 0 < r) (s : Finset ℕ)
    (hlo : ∀ j ∈ s, r / 4 < clusterScale j)
    (hhi : ∀ j ∈ s, clusterScale j ≤ (400 / 97 : ℝ) * r) : s.card ≤ 5 := by sorry
