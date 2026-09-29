-- Prove2me | Theorems.Thm_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
-- name    : IsLocalRing.exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/a360315a-29f0-583e-99c0-725e453d606f
-- title:
--   Localising a Noetherian subalgebra of a local ring
-- statement:
--   Let $A_0$ be a commutative ring and $R$ a commutative local ring, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R`, equipped with an $A_0$-algebra structure (both in the same universe), and let $T$ be an $A_0$-subalgebra of $R$ whose underlying ring is Noetherian. The assertion is that there exists an $A_0$-subalgebra $S$ of $R$ with the following three properties. First, the underlying subset of $S$ is exactly $\{x \in R : \exists\, t \in T,\ \exists\, u \in T,\ u \notin \mathfrak m \text{ and } xu = t\}$, i.e. the set of quotients in $R$ of an element of $T$ by an element of $T \setminus \mathfrak m$. Second, the ring $S$ is Noetherian and is a local ring. Third, for every $x \in S$, $x$ is a unit of $S$ if and only if its image in $R$ is a unit of $R$; equivalently, the inclusion $S \hookrightarrow R$ is a local homomorphism, the maximal ideal of $S$ being $\mathfrak m \cap S$.
--
--   This is the standard Noetherian approximation step for local rings: every Noetherian subalgebra of a local ring can be enlarged to a Noetherian local subalgebra with local inclusion, so that (taking $T$ to range over finitely generated subalgebras over a Noetherian base) $R$ is a filtered union of Noetherian local subrings. It is used in the proof of [`AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing`](thm.html#AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing), where a statement over an arbitrary local ring is reduced to the Noetherian local case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsLocalRing.exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff
    {A₀ : Type u} [CommRing A₀] {R : Type u} [CommRing R] [IsLocalRing R] [Algebra A₀ R]
    (T : Subalgebra A₀ R) [IsNoetherianRing ↥T] :
    ∃ S : Subalgebra A₀ R,
      (S : Set R) = {x : R | ∃ t ∈ T, ∃ u ∈ T, u ∉ IsLocalRing.maximalIdeal R ∧ x * u = t} ∧
      IsNoetherianRing ↥S ∧ IsLocalRing ↥S ∧ ∀ x : ↥S, IsUnit x ↔ IsUnit (x : R) := by sorry
