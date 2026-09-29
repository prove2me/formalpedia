-- Prove2me | Theorems.Thm_HomogeneousLocalization_Away_isPushout_map_of_isBaseChange
-- name    : HomogeneousLocalization.Away.isPushout_map_of_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/0ab579a8-c421-53f8-8716-d160291fadbd
-- title:
--   Degree-zero homogeneous localisation commutes with base change
-- statement:
--   Let $S$ be a commutative ring, $S'$ a commutative $S$-algebra, and let $R$ be a commutative $S$-algebra equipped with a family of $S$-submodules $\mathcal R_n \subseteq R$ ($n \in \mathbb N$) making $R$ an $\mathbb N$-graded $S$-algebra. Let $R'$ be a commutative ring that is both an $S'$-algebra and an $S$-algebra, compatibly (a scalar tower $S \to S' \to R'$), graded by $S'$-submodules $\mathcal R'_n$ making it an $\mathbb N$-graded $S'$-algebra. Let $\vartheta : R \to R'$ be an $S$-algebra map with $\vartheta(\mathcal R_n) \subseteq \mathcal R'_n$ for all $n$, and assume that for each $n$ the induced $S$-linear map $\mathcal R_n \to \mathcal R'_n$ (the target viewed as an $S$-module by restriction of scalars) exhibits $\mathcal R'_n$ as the base change of $\mathcal R_n$ along $S \to S'$, i.e. satisfies `IsBaseChange S'`. Fix $d \in \mathbb N$ and $r \in \mathcal R_d$. Write $\vartheta$, together with its degree-preservation, as a graded ring homomorphism $\mathcal R \to \mathcal R'$. Then the square of commutative rings whose horizontal maps are the composites $S \to R \to \mathcal R_0 \to$ `HomogeneousLocalization.Away 𝓡 r` and $S' \to R' \to \mathcal R'_0 \to$ `HomogeneousLocalization.Away 𝓡' (ϑ r)` (structure map, degree-zero projection `GradedRing.projZeroRingHom'`, and `HomogeneousLocalization.fromZeroRingHom` into the degree-zero part of the localisation at the powers of $r$, respectively of $\vartheta r$), whose left vertical map is $S \to S'$ and whose right vertical map is `HomogeneousLocalization.Away.map` of $\vartheta$, is a pushout square in `CommRingCat`; equivalently, `Away 𝓡' (ϑ r)` $\cong S' \otimes_S$ `Away 𝓡 r`.
--
--   This is the affine-chart form of the statement that the formation of $\operatorname{Proj}$ of a graded algebra commutes with base change: the basic open $D_+(r)$ of $\operatorname{Proj} R$, which is the spectrum of the degree-zero part of the localisation of $R$ at $r$, has base change $D_+(\vartheta r) \subseteq \operatorname{Proj} R'$. It is used to prove [`AlgebraicGeometry.GradedOAlgebra.isPullback_projMap_of_isBaseChange`](thm.html#AlgebraicGeometry.GradedOAlgebra.isPullback_projMap_of_isBaseChange), the corresponding pullback square of schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HomogeneousLocalization_Away_isPushout_map_of_isBaseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization

theorem HomogeneousLocalization.Away.isPushout_map_of_isBaseChange
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ϑ : R →ₐ[S] R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hbc : ∀ n, IsBaseChange S' ((ϑ.toLinearMap.restrict (p := 𝓡 n) (q := (𝓡' n).restrictScalars S) (hϑdeg n))
      : 𝓡 n →ₗ[S] (𝓡' n).restrictScalars S))
    {d : ℕ} (r : R) (hr : r ∈ 𝓡 d) :
    IsPushout
      (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom 𝓡 (Submonoid.powers r)).comp
        ((GradedRing.projZeroRingHom' 𝓡).comp (algebraMap S R))))
      (CommRingCat.ofHom (algebraMap S S'))
      (CommRingCat.ofHom (HomogeneousLocalization.Away.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') r))
      (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom 𝓡'
          (Submonoid.powers (({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') r))).comp
        ((GradedRing.projZeroRingHom' 𝓡').comp (algebraMap S' R')))) := by sorry
