-- Prove2me | Theorems.Thm_NoHair_kerrNewman_asymptoticComponentBounds
-- name    : NoHair.kerrNewman_asymptoticComponentBounds
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T20:08:27.011298+00:00
-- url     : https://prove2.me/theorems/be9fb68c-e6d9-469c-9a0a-1a3092dd3963
-- title:
--   Uniform asymptotic bounds for the Cartesian Kerr–Newman fields
-- statement:
--   Let $m,a,e$ be real parameters for the Kerr–Newman fields in Cartesian Kerr–Schild coordinates, and write $\rho=\sqrt{x^2+y^2+z^2}$. For any prescribed lower cutoff $L$, there are constants $R>\max(0,L)$ and $C$ such that $r>0$ throughout $\rho>R$ and, component by component,
--
--   $$|g_{ij}-\eta_{ij}|\le C/\rho,\qquad |\partial_k g_{ij}|\le C/\rho^2,\qquad |F_{ij}|\le C/\rho^2.$$
--
--   The same cutoff and constant work for all coordinate indices and all times. These estimates give the decay assumptions for the stationary end of the open Kerr–Newman manifold.
-- source:
--   T. Adamo and E. T. Newman, The Kerr–Newman metric: A Review, §3.1, Eqs. (3.15)–(3.16) and the radial ellipsoid equation, https://arxiv.org/abs/1410.6626v2. The three bounds are the metric, metric derivative, and field conditions in Prove2Me NoHair_spacetime, structure AsymptoticallyFlatEnd.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set

theorem NoHair.kerrNewman_asymptoticComponentBounds (m a e L : ℝ) :
    ∃ R C : ℝ, max 0 L < R ∧ ∀ y ∈ exteriorRegion R,
      0 < ksRadius a y ∧
      (∀ i j, |kerrNewmanMetric m a e y i j - minkowski i j| ≤ C / spatialRadius y) ∧
      (∀ i j k, |coordPartial (fun z => kerrNewmanMetric m a e z i j) k y| ≤ C / spatialRadius y ^ 2) ∧
      (∀ i j, |kerrNewmanField a e y i j| ≤ C / spatialRadius y ^ 2) := by sorry
