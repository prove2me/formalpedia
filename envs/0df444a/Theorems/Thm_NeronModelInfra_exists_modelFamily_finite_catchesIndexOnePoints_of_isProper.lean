-- Prove2me | Theorems.Thm_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper
-- name    : NeronModelInfra.exists_modelFamily_finite_catchesIndexOnePoints_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/e675e746-9915-5f4c-ad0a-251913ae7c7c
-- title:
--   Proper K-schemes have finite index-one-catching R-model families
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete valuation ring property) in a fixed universe, let $K$ be a field with an $R$-algebra structure making it the fraction field of $R$, let $AK$ be a scheme and let $gK : AK \to \operatorname{Spec} K$ be a proper morphism. The assertion is that there exists a `ModelFamily R K gK`, that is: an index type $\iota$, schemes $X_i$, morphisms $\mathrm{str}_i : X_i \to \operatorname{Spec} R$, and for each $i$ a chart, namely a morphism from the fibre product of $\mathrm{str}_i$ with `specGenericFibreInclusion R K` $= \operatorname{Spec}(R \to K)$ (the generic fibre of $X_i$) to $AK$ whose composite with $gK$ is the second projection to $\operatorname{Spec} K$, this morphism being an open immersion; such that (i) $\iota$ is finite; (ii) each $X_i$ is affine and each $\mathrm{str}_i$ is separated, flat, locally of finite type and quasi-compact; and (iii) the family satisfies `ModelFamily.CatchesIndexOnePoints`: for every discrete valuation domain $R'$ with an $R$-algebra structure whose structure map is a local homomorphism, with fraction field $K'$ and the compatible $K$-algebra and scalar-tower structures, such that `IsIndexOneExtension R R'` holds — i.e. the maximal ideal of $R$ extends to the maximal ideal of $R'$ and the residue field extension is formally smooth — and for every $K'$-point $a : \operatorname{Spec} K' \to AK$ over $\operatorname{Spec}(K \to K')$, there are an index $i$ and an $R'$-point $x : \operatorname{Spec} R' \to X_i$ over $\operatorname{Spec}(R \to R')$ whose associated generic-fibre $K'$-point of the generic fibre of $X_i$, followed by the chart at $i$, equals $a$.
--
--   This is the boundedness input to the construction of Néron models: properness of the generic fibre yields finitely many affine, flat, separated, finite-type $R$-models of affine open parts of $AK$ whose integral points over index-one extensions of $R$ catch all such points of $AK$, in the sense of Bosch–Lütkebohmert–Raynaud 1.1. It is used in the construction of the Néron model property bundle of the generic fibre of an abelian scheme over a henselian local ring, and its proof rests on a valuative bound for sections of proper morphisms obtained from [`AlgebraicGeometry.exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper`](thm.html#AlgebraicGeometry.exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_modelFamily_finite_catchesIndexOnePoints_of_isProper.lean

import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_modelFamily_finite_catchesIndexOnePoints_of_isProper
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} (gK : AK ⟶ Spec (CommRingCat.of K)) [IsProper gK] :
    ∃ M : ModelFamily R K gK, Finite M.ι ∧
      (∀ i, IsAffine (M.X i) ∧ IsSeparated (M.str i) ∧ Flat (M.str i) ∧
        LocallyOfFiniteType (M.str i) ∧ QuasiCompact (M.str i)) ∧
      M.CatchesIndexOnePoints := by sorry
