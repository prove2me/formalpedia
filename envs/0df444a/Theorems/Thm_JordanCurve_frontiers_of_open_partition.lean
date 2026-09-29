-- Prove2me | Theorems.Thm_JordanCurve_frontiers_of_open_partition
-- name    : JordanCurve.frontiers_of_open_partition
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T00:15:55.074445+00:00
-- url     : https://prove2.me/theorems/fd151c10-05c1-4540-9a87-ecab82f3d4fa
-- title:
--   Frontiers of an open two-region partition
-- statement:
--   If disjoint open sets $U,V$ cover the complement of a set $J$, and every point of $J$ belongs to both $\overline U$ and $\overline V$, then $$\partial U=J=\partial V.$$ This elementary topological step turns two-sided accessibility into the boundary conclusion of Jordan separation.
-- source:
--   Elementary topology; follows from the definitions of frontier and closure.

import Mathlib.Topology.Closure
import Mathlib.Topology.Connected.Basic

namespace JordanCurve
theorem frontiers_of_open_partition {X : Type*} [TopologicalSpace X]
    (J U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : U ∪ V = Jᶜ)
    (haccess : J ⊆ closure U ∩ closure V) :
    frontier U = J ∧ frontier V = J := by sorry
end JordanCurve
