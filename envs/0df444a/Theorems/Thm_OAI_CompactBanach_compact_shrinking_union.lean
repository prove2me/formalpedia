-- Prove2me | Theorems.Thm_OAI_CompactBanach_compact_shrinking_union
-- name    : OAI.CompactBanach.compact_shrinking_union
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:12:51.584378+00:00
-- url     : https://prove2.me/theorems/938f888e-a98a-4bdb-851c-c272e95da28e
-- title:
--   A point together with finite sets converging to it forms a compact set
-- statement:
--   Let $(B,d)$ be a metric space, $o\in B$ a point, and $(C_j)_{j\in\mathbb{N}}$ a sequence of finite subsets of $B$ that shrink to $o$ in the following sense: for every $\varepsilon>0$ there is $N\in\mathbb{N}$ such that $d(z,o)<\varepsilon$ for every $j\ge N$ and every $z\in C_j$.
--
--   **Theorem.** Under this hypothesis the set
--   $$
--   K=\{o\}\cup\bigcup_{j\in\mathbb{N}}C_j
--   $$
--   is compact.
--
--   This is the compactness half of the construction of the compact doubling set: finite clusters placed at distances tending to zero from a base point form, together with that point, a compact set, regardless of the internal shape of the clusters.
--
--   **Formalization Note** The sets $C_j$ are given as `Finset B`, and the conclusion is `IsCompact` of the union of the singleton with all of them.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/CompactUnion.lean#L10-L38

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

theorem OAI.CompactBanach.compact_shrinking_union {B : Type*} [MetricSpace B]
    (o : B) (C : ℕ → Finset B)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ z ∈ C j, dist z o < ε) :
    IsCompact ({o} ∪ ⋃ j : ℕ, (C j : Set B)) := by sorry
