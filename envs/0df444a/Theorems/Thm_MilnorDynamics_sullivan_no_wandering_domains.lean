-- Prove2me | Theorems.Thm_MilnorDynamics_sullivan_no_wandering_domains
-- name    : MilnorDynamics.sullivan_no_wandering_domains
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T12:57:56.682787+00:00
-- url     : https://prove2.me/theorems/ab5aa18a-6ccc-48c0-93c3-6a21fe83457c
-- title:
--   Theorem 16.4 (Sullivan) — every Fatou component is eventually periodic
-- statement:
--   **Sullivan's Nonwandering Theorem.** Let $f$ be a rational map of the Riemann sphere of degree $d\ge 2$. Every Fatou component $U$ of $f$ is eventually periodic: there exist integers $n\ge 0$ and $p\ge 1$ such that the $n$-th forward image $f^{\circ n}(U)$ is mapped onto itself by $f^{\circ p}$,
--
--   $$f^{\circ p}\bigl(f^{\circ n}(U)\bigr)=f^{\circ n}(U).$$
--
--   In other words, a rational map has no **wandering domains**. Combined with the classification of periodic Fatou components (Theorem 16.1, applied to $f^{\circ p}$), it shows that the dynamics on the whole Fatou set is described by attracting basins, parabolic basins, Siegel disks and Herman rings.
--
--   **Formalization Note** Only the first sentence of Milnor's Theorem 16.4 is formalized; the "in particular" sentence is a consequence of it together with Theorem 16.1. The degree bound $d\ge2$ is Milnor's standing hypothesis in §16 ("nonlinear rational map").
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §16, p. 171, Theorem 16.4 (Sullivan Nonwandering Theorem), first sentence; Sullivan, Ann. of Math. 122 (1985)

import Mathlib
import Definitions.Def_MilnorDynamics_FatouComponents

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem sullivan_no_wandering_domains (f : RationalMap) (hf : 2 ≤ f.degree)
    (U : Set (OnePoint ℂ)) (hU : IsFatouComponent f.toFun U) :
    ∃ n p : ℕ, 1 ≤ p ∧ f.toFun^[p] '' (f.toFun^[n] '' U) = f.toFun^[n] '' U := by sorry

end MilnorDynamics
