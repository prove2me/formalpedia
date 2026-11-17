-- Prove2me | Theorems.Thm_N25_LocalFive_finite_schemeHomOver_of_finite_field
-- name    : N25.LocalFive.finite_schemeHomOver_of_finite_field
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:49.304244+00:00
-- url     : https://prove2.me/theorems/7022803d-bbb9-49d3-910f-2ca0ac0712c9
-- title:
--   A finite field has finitely many points on a quasi-compact finite-type scheme
-- statement:
--   Let $R$ be a commutative ring, let $k$ be a finite field equipped with an $R$-algebra structure, and let $f:X\to\mathrm{Spec}(R)$ be quasi-compact and locally of finite type. Then the set of morphisms $\mathrm{Spec}(k)\to X$ over $\mathrm{Spec}(R)$ is finite: $$|X(k)|=|\mathrm{Hom}_{\mathrm{Spec}(R)}(\mathrm{Spec}(k),X)|<\infty.$$ This is the scheme-theoretic finiteness theorem behind the finite reduction quotient.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem N25.LocalFive.finite_schemeHomOver_of_finite_field
    {R k : Type} [CommRing R] [Field k]
    [Algebra R k] [Finite k]
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    Finite (SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R k))) f)  := by sorry
