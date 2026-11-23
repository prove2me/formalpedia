-- Prove2me | Theorems.Thm_NoHair_static_conformal_halves_signed_lapse_equation
-- name    : NoHair.static_conformal_halves_signed_lapse_equation
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:31:06.0025+00:00
-- url     : https://prove2.me/theorems/5e82b052-34fe-434f-98f5-d434edee26b8
-- title:
--   Weighted signed lapse equation on both conformal copies
-- statement:
--   On each closed physical copy take $V=sN$ for $s=\pm1$, and $k=((1+V)/2)^4 h$. In the original smooth spatial coordinates the vector density $\sqrt{\det k}\,(2/(1+V))^2 k^{ij}\partial_j V$ has zero divergence at every finite point up to the horizon. The conformal factors cancel and the density equals $s\sqrt{\det h}\,h^{ij}\partial_j N$.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticConformalCompletion

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.static_conformal_halves_signed_lapse_equation (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∀ x ∈ closure Ω, ∀ s : ℝ, s=1 ∨ s=-1 →
      staticWeightedLapseDivergence (staticPositiveMetric (fun y => s*N y) h) (fun y => s*N y) x = 0 := by sorry
