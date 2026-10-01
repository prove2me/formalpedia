-- Prove2me | Theorems.Thm_MilnorDynamics_exists_sphere_ne_zero_of_analytic
-- name    : MilnorDynamics.exists_sphere_ne_zero_of_analytic
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T23:04:55.353899+00:00
-- url     : https://prove2.me/theorems/c5ed10af-29bb-4796-9e78-19ccd3aece72
-- title:
--   Isolated zeros - an analytic function that is not identically zero is nonzero on some circle
-- statement:
--   **Isolated zeros, in usable form.** Let $U\subseteq\mathbb C$ be a domain, let $G$ be analytic on $U$, and suppose $G$ is not identically zero on $U$. Then for every $z_0\in U$ there is a radius $r>0$ such that the closed disc of radius $r$ about $z_0$ lies in $U$ and $G$ is nonzero on its boundary circle:
--
--   $$\exists r>0,\qquad \overline{D(z_0,r)}\subseteq U \quad\text{and}\quad \forall z\in U,\ |z-z_0|=r\implies G(z)\neq 0 .$$
--
--   This is the principle of isolated zeros made quantitative. The zero set of a nonzero analytic function on a connected open set is discrete, so at each point of $U$ there is a punctured neighbourhood free of zeros; choosing the radius smaller than both that punctured neighbourhood and a disc contained in $U$ gives the circle. The statement is the topological half of Hurwitz's theorem for limits: it is what lets a boundary circle be chosen on which the limit is bounded away from the value being omitted.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; the isolated-zeros property of nonconstant analytic functions is the standard ingredient of Hurwitz's theorem.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem exists_sphere_ne_zero_of_analytic (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G U) (z0 : ℂ) (hz0 : z0 ∈ U)
    (hne : ∃ w ∈ U, G w ≠ 0) :
    ∃ r > 0, Metric.closedBall z0 r ⊆ U ∧ ∀ z ∈ Metric.sphere z0 r, G z ≠ 0 := by sorry

end MilnorDynamics
