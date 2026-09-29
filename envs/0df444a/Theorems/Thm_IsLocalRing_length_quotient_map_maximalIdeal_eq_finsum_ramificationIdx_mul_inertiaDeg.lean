-- Prove2me | Theorems.Thm_IsLocalRing_length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg
-- name    : IsLocalRing.length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/0e727584-1629-554d-81ab-3929da5c9939
-- title:
--   Length of the special fibre of D as sum ef
-- statement:
--   Let $C$ be a discrete valuation ring (a Noetherian local domain that is a DVR) with fraction field $K$, and let $D$ be a Noetherian local domain which is a $C$-algebra and satisfies: for every $c \in C$ the image $\mathrm{algebraMap}\ C\ D\ c$ lies in $\mathfrak m_D$ if and only if $c \in \mathfrak m_C$; every $d \in D$ is congruent modulo $\mathfrak m_D$ to the image of some $c \in C$ (so $C \to D$ is local and induces a surjection on residue fields); $D$ has dimension at most one in the sense of `Ring.DimensionLEOne`; and $\mathfrak m_D \neq 0$. Let $\kappa$ be a field that is a fraction field of $D$, equipped with compatible $C$- and $K$-algebra structures making $C \to D \to \kappa$ and $C \to K \to \kappa$ scalar towers, with $\kappa/K$ finite and separable. The conclusion has two parts: first, the set of valuation subrings $B \subseteq \kappa$ containing the image of $D$ is finite; second, the $D$-module length of $D/\mathfrak m_C D$, where $\mathfrak m_C D$ denotes the image ideal $(\mathfrak m_C).\mathrm{map}(\mathrm{algebraMap}\ C\ D)$, equals, as an element of $\mathbb N^\infty$, the finite sum over those valuation subrings $B$ of $\kappa$ that contain the images of $C$ and of $D$ and satisfy, for $c \in C$, that $\mathrm{algebraMap}\ C\ \kappa\ c$ is a non-unit of $B$ exactly when $c \in \mathfrak m_C$, of the product $e \cdot f$ of the ramification index `ramificationIdx'` and inertia degree `inertiaDeg'` of $\mathfrak m_C$ with respect to $\mathfrak m_B$, computed for the $C$-algebra structure on $B$ obtained by restricting $\mathrm{algebraMap}\ C\ \kappa$ to $B$.
--
--   This is the classical statement that the intersection multiplicity of a one-dimensional local ring with the special fibre equals the sum of the local degrees $ef$ of its branches, the valuation subrings of the fraction field centred on $\mathfrak m_C$ playing the role of branches. It is used by [`IsLocalRing.finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal`](thm.html#IsLocalRing.finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal) in the counting of points on the special fibre, and its proof invokes [`IsDiscreteValuationRing.exists_finite_locallyPrincipalOverring`](thm.html#IsDiscreteValuationRing.exists_finite_locallyPrincipalOverring) to produce a finite, locally principal overring of $D$ inside $\kappa$ containing all elements integral over $C$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D] [Algebra C D]
    (hDmax : ∀ c : C, algebraMap C D c ∈ maximalIdeal D ↔ c ∈ maximalIdeal C)
    (hDres : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ maximalIdeal D)
    (hDdim : Ring.DimensionLEOne D) (hDnf : maximalIdeal D ≠ ⊥)
    (κ : Type*) [Field κ] [Algebra D κ] [IsFractionRing D κ] [Algebra C κ] [IsScalarTower C D κ]
    [Algebra K κ] [IsScalarTower C K κ] [FiniteDimensional K κ] [Algebra.IsSeparable K κ] :
    {B : ValuationSubring κ | ∀ d : D, algebraMap D κ d ∈ B}.Finite ∧
    Module.length D (D ⧸ (maximalIdeal C).map (algebraMap C D)) =
      ∑ᶠ B : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ d : D, algebraMap D κ d ∈ B) ∧
          ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C},
        ((letI : Algebra C ↥B.1 := ((algebraMap C κ).codRestrict B.1 B.2.1).toAlgebra
          (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B.1) * (maximalIdeal C).inertiaDeg' (maximalIdeal ↥B.1) : ℕ) : ℕ∞) := by sorry
