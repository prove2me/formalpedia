-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_realBox_disjoint_iff
-- name    : OAI.BoxTransport.Routing.realBox_disjoint_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:11:10.796507+00:00
-- url     : https://prove2.me/theorems/9524e63d-0d66-44a8-9324-a16e8266aef5
-- title:
--   Two closed boxes are disjoint iff some coordinate gap exceeds the sum of their half-widths
-- statement:
--   For $c,r\in\mathbb{R}^3$ let
--
--   $$B(c,r)=\{x\in\mathbb{R}^3:\ |x_j-c_j|\le r_j\ \text{ for } j=1,2,3\}$$
--
--   be the closed axis-parallel box with center $c$ and half-widths $r_1,r_2,r_3$.
--
--   **Theorem.** Let $c,d,h,k\in\mathbb{R}^3$ with $h_j\ge 0$ and $k_j\ge 0$ for $j=1,2,3$. Then
--
--   $$B(c,h)\cap B(d,k)=\varnothing\quad\Longleftrightarrow\quad h_j+k_j<|c_j-d_j|\ \text{ for some } j\in\{1,2,3\}.$$
--
--   Two closed boxes are disjoint exactly when their projections to some coordinate axis are disjoint intervals. The criterion converts disjointness of boxes into a strict numerical gap in a single coordinate and back, which is the form needed to show that disjoint boxes stay disjoint after small enlargements, translations or expansions.
--
--   **Formalization Note** The box $B(c,r)$ is `realBox c r`, points of $\mathbb{R}^3$ are functions on `Fin 3`, and disjointness is Mathlib's `Disjoint` for sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Geometry.lean#L80-L113

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry

open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.realBox_disjoint_iff {c d h k : Space}
    (hh : ∀ j, 0 ≤ h j) (hk : ∀ j, 0 ≤ k j) :
    Disjoint (realBox c h) (realBox d k) ↔
      ∃ j, h j + k j < |c j - d j| := by sorry
