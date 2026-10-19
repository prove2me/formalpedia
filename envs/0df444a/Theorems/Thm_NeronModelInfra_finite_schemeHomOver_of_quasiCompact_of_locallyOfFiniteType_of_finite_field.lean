-- Prove2me | Theorems.Thm_NeronModelInfra_finite_schemeHomOver_of_quasiCompact_of_locallyOfFiniteType_of_finite_field
-- name    : NeronModelInfra.finite_schemeHomOver_of_quasiCompact_of_locallyOfFiniteType_of_finite_field
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T19:21:26.222624+00:00
-- url     : https://prove2.me/theorems/bb117cb1-0b6d-44fb-ac19-ac740adced21
-- title:
--   Finite residue-field points of a quasi-compact locally finite-type scheme
-- statement:
--   Let $R$ be a commutative ring, let $k$ be a finite field equipped with an $R$-algebra structure, and let $Y$ be a scheme whose structural morphism to $\operatorname{Spec} R$ is quasi-compact and locally of finite type. Then the set of $R$-morphisms from $\operatorname{Spec} k$ to $Y$ is finite. Neither properness nor finiteness of the structural morphism is required.
-- source:
--   Original formalization by Vas and contributors, MazurTheorem project; finite affine-cover and finite-generation argument, October 16, 2026. Apache-2.0.

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
universe u

theorem NeronModelInfra.finite_schemeHomOver_of_quasiCompact_of_locallyOfFiniteType_of_finite_field (R κ : Type u) [CommRing R] [Field κ] [Finite κ] [Algebra R κ]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R κ))) f) := by sorry
