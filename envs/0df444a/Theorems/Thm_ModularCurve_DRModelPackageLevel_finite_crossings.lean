-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_finite_crossings
-- name    : ModularCurve.DRModelPackageLevel.finite_crossings
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/bbe7ecc1-59a2-5f9b-adb8-e8f1449b5314
-- title:
--   Finiteness of the crossings in the special fibre
-- statement:
--   Let $N_0$ be a nonzero natural number and $q$ a prime with $q \nmid N_0$, and let $\mathfrak{X}$ be a [`ModularCurve.DRModelPackageLevel N₀ q hqN`](def/ModularCurve_DRModelPackageLevel.html#L71), i.e. a bundle of data and properties for the Igusa-type scheme [`ModularCurve.DRLevel.X N₀ q`](def/ModularCurve_DRModelPackageLevel.html#L34) over $\operatorname{Spec}$ of [`ModularCurve.DRLevel.R q`](def/ModularCurve_DRModelPackageLevel.html#L32), the subring of $\mathbb{Q}$ consisting of rationals whose denominator is coprime to $q$: the structure morphism is proper, flat and locally of finite presentation, the total space is integral and integrally closed on affine opens, its generic fibre is smooth of relative dimension $1$ and geometrically integral, a `CurveModel` over $\overline{\mathbb{Q}}$ with function field the base change `modularFunctionFieldBar (N₀ * q)` is given together with an isomorphism onto the $\overline{\mathbb{Q}}$-fibre, compatibility of places with the arithmetic Galois action, a pinning of the chart algebra `chartAlgFin (N₀ * q) q` in terms of Laurent expansions, two sections $\varepsilon_\infty,\varepsilon_0$ over the base, and further data, summarised here. Let $\kappa$ be an algebraically closed field of characteristic $q$ and $\mathrm{to}\kappa :$ `R q` $\to \kappa$ a ring homomorphism. The assertion is that the type of points of the scheme-theoretic fibre product of the two morphisms $\mathfrak{X}.\mathrm{comp}\,\kappa\,\mathrm{to}\kappa\,0$ and $\mathfrak{X}.\mathrm{comp}\,\kappa\,\mathrm{to}\kappa\,1$ provided by the package, the two components of the geometric special fibre at $q$, is finite.
--
--   This is the finiteness of the set of crossing points (nodes) of the two components of the mod $q$ fibre of $X_0(N_0q)$, classically the supersingular points of the Deligne–Rapoport fibre. It is used wherever the dual graph of that special fibre must be finite, for instance in the construction of the resolved regular model and in the analysis of branch ideals at the nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_finite_crossings.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.DRModelPackageLevel.finite_crossings {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀}
    (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : ModularCurve.DRLevel.R q →+* κ) :
    Finite ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1)) := by sorry
