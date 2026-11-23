-- Prove2me | Theorems.Thm_NoHair_spatial_conformal_connection
-- name    : NoHair.spatial_conformal_connection
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:57:17.278578+00:00
-- url     : https://prove2.me/theorems/a2a1963c-55f7-43f2-aa05-54ce6191a9ad
-- title:
--   Levi-Civita connection of a conformally rescaled spatial metric
-- statement:
--   For $k=u^4h$ the inverse metric is $u^{-4}h^{-1}$. The connection differs from that of $h$ by $\delta^a_i p_j+\delta^a_j p_i-h_{ij}p^a$, where $p_i=2\partial_i u/u$. Both identities hold in arbitrary coordinates at each point where $u\ne0$.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.spatial_conformal_connection (u : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hu : ContDiffOn ℝ ∞ u W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (x : ADMPoint) (hx : x ∈ W) (hn : u x ≠ 0) :
    let k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ := fun y => (u y ^ 4) • h y
    (k x)⁻¹ = ((u x ^ 4)⁻¹) • (h x)⁻¹ ∧
    ∀ a i j : Fin 3, spatialLeviCivita k x a i j = spatialLeviCivita h x a i j +
      (if a=i then 1 else 0) * (2/u x * spatialADMPartial j u x) +
      (if a=j then 1 else 0) * (2/u x * spatialADMPartial i u x) -
      h x i j * (2/u x * staticRaisedGradient u h a x) := by sorry
