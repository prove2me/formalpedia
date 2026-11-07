-- Prove2me | Theorems.Thm_LosslessQLTC_corollary_3_4
-- name    : LosslessQLTC.corollary_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:22:01.807729+00:00
-- url     : https://prove2.me/theorems/31e955da-a415-406a-970a-8adf49953186
-- title:
--   Corollary 3.4, p.22 — every ordered endpoint map is surjective
-- statement:
--   Let $v\in V_\emptyset$ and $I\subseteq[k]$. For every ordering $\pi$ of $I$, the endpoint map $\mathrm{End}_\pi$ onto $\mathrm{Lk}_I(v)$ is surjective: every $x\in\mathrm{Lk}_I(v)$ is reached by a monotone path from $v$ with direction order $\pi$. So the link level above $I$ can be built one direction at a time, in any order.
--
--   Differences from the source:
--   - encoding: a decorated $(k,2)$-cubical complex with blocks $V_I$ and cubes $X(i)$ for all $i$, directions $1,\dots,k$ → `SquareComplex k`: one vertex type with a type map, the graph and $X(2)$ only, directions `Fin k`; reason: $X(0),X(1)$ are forced, no result uses $X(i)$ for $i\ge3$, and any such data extends with $X(i)=\emptyset$ for $i\ge3$
--   - encoding: an ordering $\pi$ of $I$ and the map $\mathrm{End}_\pi$ → a duplicate-free list and nonemptiness of each fiber over $\mathrm{Lk}_I(v)$; reason: same statement
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Corollary 3.4, p.22

import Mathlib
import Definitions.Def_LosslessQLTC_Paths

namespace LosslessQLTC

/-- Corollary 3.4 (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.22): for `v ∈ V_∅` and every
ordering `π` of `I`, the endpoint map `End_π` onto `Lk_I(v)` is surjective. -/
theorem corollary_3_4 {k : ℕ} (X : SquareComplex k) (v : X.Vtx) (hv : X.type v = ∅)
    (I : Finset (Fin k)) (π : List (Fin k)) (hπ : IsOrdering π I) (x : X.Vtx)
    (hx : x ∈ LkType X v I) :
    (fiber X v π x).Nonempty := by sorry

end LosslessQLTC
