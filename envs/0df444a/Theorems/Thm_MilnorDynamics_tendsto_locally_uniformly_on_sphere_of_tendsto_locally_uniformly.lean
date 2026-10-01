-- Prove2me | Theorems.Thm_MilnorDynamics_tendsto_locally_uniformly_on_sphere_of_tendsto_locally_uniformly
-- name    : MilnorDynamics.tendsto_locally_uniformly_on_sphere_of_tendsto_locally_uniformly
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T21:33:21.810185+00:00
-- url     : https://prove2.me/theorems/6b95cf47-8b49-4cf1-b578-d76e41045d12
-- title:
--   Euclidean-to-chordal transport - planar local uniform convergence lifts to the sphere
-- statement:
--   **Euclidean-to-chordal transport for locally uniform convergence.** Let $U\subseteq\mathbb C$ be an open set and let $F_n:\mathbb C\to\mathbb C$ converge to $g:\mathbb C\to\mathbb C$ locally uniformly on $U$ in the ordinary Euclidean sense. Then the family obtained by viewing each $F_n$ and $g$ as maps into the Riemann sphere $\hat{\mathbb C}$ through the affine chart converges to $g$, locally uniformly on $U$, with respect to the chordal (spherical) metric.
--
--   The point is that on finite values the chordal distance is controlled by the Euclidean one, $$\sigma(z,w)=\frac{2|z-w|}{\sqrt{1+|z|^2}\,\sqrt{1+|w|^2}}\le 2|z-w| ,$$ because both square roots are at least $1$.  Hence Euclidean locally uniform convergence on each compact subset of $U$ upgrades to chordal locally uniform convergence, and the two notions of locally uniform convergence used by the mission's definition file agree on finite-valued families.  This is the step that lets the planar normality children -- stated in terms of `TendstoLocallyUniformlyOn` -- be read back in the sphere-valued language of `IsNormalFamily`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, Lemma 3.1(a), p. 33 (locally uniform convergence on the sphere is uniform convergence in the chordal metric on compacta; the spherical metric is equivalent to the Euclidean metric on compacta of the finite plane).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem tendsto_locally_uniformly_on_sphere_of_tendsto_locally_uniformly
    (U : Set ℂ) (hU : IsOpen U) (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hcv : TendstoLocallyUniformlyOn F g atTop U) :
    TendstoLocallyUniformlyOnSphere (fun n z => ((F n z : ℂ) : OnePoint ℂ))
      (fun z => ((g z : ℂ) : OnePoint ℂ)) U := by sorry

end MilnorDynamics
