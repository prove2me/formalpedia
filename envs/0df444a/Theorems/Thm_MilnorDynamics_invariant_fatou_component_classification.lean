-- Prove2me | Theorems.Thm_MilnorDynamics_invariant_fatou_component_classification
-- name    : MilnorDynamics.invariant_fatou_component_classification
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T12:47:31.380247+00:00
-- url     : https://prove2.me/theorems/85ead4f8-6058-421e-ad80-4d1eb1e9b35c
-- title:
--   Theorem 16.1 — classification of invariant Fatou components
-- statement:
--   Let $f$ be a rational map of the Riemann sphere of degree $d\ge 2$ and let $U$ be a Fatou component (a connected component of the Fatou set) which $f$ maps onto itself, $f(U)=U$. Then there are just four possibilities:
--
--   1. $U$ is the **immediate basin of an attracting fixed point**: $U$ contains a fixed point $p$ with multiplier $|\lambda|<1$, and $U$ is the connected component containing $p$ of the basin of $p$;
--   2. $U$ is the **immediate basin of one petal of a parabolic fixed point** with multiplier $\lambda=1$: there is a fixed point $p\in\partial U$ with $\lambda=1$ such that every orbit in $U$ converges to $p$;
--   3. $U$ is a **Siegel disk**; or
--   4. $U$ is a **Herman ring**.
--
--   (The superattracting case $\lambda=0$ is included in case 1.) Together with Sullivan's theorem that every Fatou component is eventually periodic, this gives a complete description of the dynamics on the Fatou set.
--
--   **Formalization Note** Case 2 is encoded by its defining dynamical property: an invariant Fatou component all of whose orbits converge to a boundary fixed point of multiplier exactly $1$ (Milnor's case (b) on p. 167, with the conclusion of the theorem that the boundary fixed point is parabolic with $\lambda=1$). Siegel disks and Herman rings are as in the definition file `MilnorDynamics_FatouComponents`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §16, p. 167, Theorem 16.1

import Mathlib
import Definitions.Def_MilnorDynamics_FatouComponents

open scoped OnePoint Topology
open Filter Set

namespace MilnorDynamics

theorem invariant_fatou_component_classification (f : RationalMap) (hf : 2 ≤ f.degree)
    (U : Set (OnePoint ℂ)) (hU : IsFatouComponent f.toFun U) (hinv : f.toFun '' U = U) :
    (∃ p ∈ U, f.toFun p = p ∧ ‖multiplier f.toFun p‖ < 1 ∧ U = immediateBasin f.toFun p) ∨
    (∃ p ∈ frontier U, f.toFun p = p ∧ multiplier f.toFun p = 1 ∧
      ∀ z ∈ U, Tendsto (fun n : ℕ => f.toFun^[n] z) atTop (𝓝 p)) ∨
    IsSiegelDisk f.toFun U ∨ IsHermanRing f.toFun U := by sorry

end MilnorDynamics
