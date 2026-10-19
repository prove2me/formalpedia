-- Prove2me | Theorems.Thm_OAI_CriticalZ3_nearestNeighbor_exit_boundary
-- name    : OAI.CriticalZ3.nearestNeighbor_exit_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:45:04.937053+00:00
-- url     : https://prove2.me/theorems/33b100be-3338-46ee-887d-1c7d1495c914
-- title:
--   Nearest-neighbour exits from a cube leave through its boundary
-- statement:
--   If $x$ lies in the cube $\Lambda_n(c)\subseteq\mathbb Z^3$, $y$ lies outside it, and $x,y$ are nearest neighbours, then $x$ is a boundary point of the cube:
--   $$
--   x_i=c_i\pm n\quad\text{for some }i .
--   $$
--
--   Together with the first-exit lemma, this shows that a path leaving a cube passes through its boundary.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Basic.lean#L575-L602

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic

open OAI OAI.CriticalZ3
universe uE uOmega uV
open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology

theorem OAI.CriticalZ3.nearestNeighbor_exit_boundary {c x y : Vertex} {n : ℕ}
    (hx : x ∈ cube c n) (hy : y ∉ cube c n) (hxy : NearestNeighbor x y) :
    x ∈ cubeBoundary c n := by sorry
