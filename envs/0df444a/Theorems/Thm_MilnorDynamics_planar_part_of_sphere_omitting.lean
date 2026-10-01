-- Prove2me | Theorems.Thm_MilnorDynamics_planar_part_of_sphere_omitting
-- name    : MilnorDynamics.planar_part_of_sphere_omitting
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T18:52:30.210536+00:00
-- url     : https://prove2.me/theorems/ebb9dfa6-07c5-44da-919a-251f6685e61a
-- title:
--   Sphere-to-plane bridge - a holomorphic map omitting 0, 1, infinity is planar
-- statement:
--   **Bridge from the Riemann sphere to the plane.** Let $U\subseteq\mathbb C$ be an open set and let $g:U\to\hat{\mathbb C}$ be a map into the Riemann sphere that is holomorphic in the coordinate-chart sense of `IsHolomorphicOn` and that omits the three values $0$, $1$ and $\infty$ on $U$. Then the finite chart of the sphere turns $g$ into a genuine complex-valued map $\hat g:U\to\mathbb C$ with $\hat g(z)=g(z)$, which is complex differentiable on $U$ and whose values lie in $\mathbb C\setminus\{0,1\}$. Concretely there is $\hat g:\mathbb C\to\mathbb C$ with $\hat g$ complex differentiable on $U$, with $\hat g(U)\subseteq\mathbb C\setminus\{0,1\}$, and with $g(z)=\hat g(z)$ for all $z\in U$.
--
--   The point is that omitting $\infty$ removes the second chart of the sphere entirely, so the chart-wise definition of holomorphy collapses to ordinary complex differentiability on $U$. This is the step that lets every planar statement on the board -- Arzela-Ascoli extraction, the escape lemma, and Corollary 3.3 on $\mathbb C\setminus\{0,1\}$ -- be applied to a family of sphere-valued maps that omits $0$, $1$ and $\infty$, which is exactly the normalised core of Milnor's Theorem 3.7.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §3, pp. 32-33 (the two standard coordinate charts z and 1/z on the Riemann sphere and the reading of a holomorphic map U -> C^ in those charts); the bridge is the formalisation note of the mission definition MilnorDynamics_NormalFamilies, under which a map omitting infinity is planar.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem planar_part_of_sphere_omitting (U : Set ℂ) (g : ℂ → OnePoint ℂ)
    (hg : IsHolomorphicOn U g)
    (homit : ∀ z ∈ U, g z ≠ ((0 : ℂ) : OnePoint ℂ) ∧
      g z ≠ ((1 : ℂ) : OnePoint ℂ) ∧ g z ≠ ∞) :
    ∃ ĝ : ℂ → ℂ, DifferentiableOn ℂ ĝ U ∧ MapsTo ĝ U ({0, 1}ᶜ : Set ℂ) ∧
      ∀ z ∈ U, ((ĝ z : ℂ) : OnePoint ℂ) = g z := by sorry

end MilnorDynamics
