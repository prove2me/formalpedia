-- Prove2me | Theorems.Thm_Module_Invertible_bijective_localizedModule_map_of_not_range_le
-- name    : Module.Invertible.bijective_localizedModule_map_of_not_range_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/49ed09e3-b1d0-52c8-86a0-a5f09019dd01
-- title:
--   Bijectivity at a prime of a map of invertible modules
-- statement:
--   Let $R$ be a commutative ring and let $P$ and $Q$ be $R$-modules, each carrying the Mathlib typeclass `Module.Invertible R _` (so each is an invertible, i.e. locally free of rank one, $R$-module). Let $f : P \to Q$ be an $R$-linear map and let $x$ be a point of the prime spectrum of $R$, with associated prime ideal $\mathfrak p =$ `x.asIdeal`. Assume that the image of $f$ is not contained in the submodule $\mathfrak p \cdot Q$, that is, `LinearMap.range f` is not $\le$ `x.asIdeal • (⊤ : Submodule R Q)`. The conclusion is that the induced map on localisations at the multiplicative set $S = R \setminus \mathfrak p$ (`x.asIdeal.primeCompl`), namely `LocalizedModule.map x.asIdeal.primeCompl f` from $P_{\mathfrak p}$ to $Q_{\mathfrak p}$, is bijective as a function. Thus a linear map between invertible modules which is nonzero on the fibre at $\mathfrak p$ becomes an isomorphism after localising at $\mathfrak p$.
--
--   This is the standard local criterion for a morphism of line bundles to be an isomorphism at a point: vanishing of the map on the fibre at $\mathfrak p$ is the only obstruction. It is used in the treatment of the chart-local Drinfeld quadruples in the Čerednik–Drinfeld material, where several branches require knowing that a comparison map of invertible modules is invertible away from a stratum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Invertible_bijective_localizedModule_map_of_not_range_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.Invertible.bijective_localizedModule_map_of_not_range_le
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Invertible R P] [Module.Invertible R Q] (f : P →ₗ[R] Q) (x : PrimeSpectrum R)
    (hx : ¬ LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)) :
    Function.Bijective (LocalizedModule.map x.asIdeal.primeCompl f) := by sorry
