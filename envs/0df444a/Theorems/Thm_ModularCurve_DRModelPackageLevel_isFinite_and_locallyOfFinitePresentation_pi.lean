-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_pi
-- name    : ModularCurve.DRModelPackageLevel.isFinite_and_locallyOfFinitePresentation_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/f92253be-9a63-5413-8938-f0cb7741bd77
-- title:
--   The package map π is finite and locally of finite presentation
-- statement:
--   Fix natural numbers $N_0$ and $q$, with $N_0$ nonzero and $q$ prime, together with a hypothesis $hqN$ asserting that $q \nmid N_0$, and let $\mathfrak{P}$ be a term of the structure `DRModelPackageLevel N₀ q hqN`. That structure bundles, over the Igusa scheme `X N₀ q` with its structural morphism `toBase N₀ q = IgusaScheme.igusaTo (N₀ * q) q` to $\operatorname{Spec}$ of the ring `R q`: the requirements that this morphism be proper, flat and locally of finite presentation, that `X N₀ q` be integral and that the sections over every affine open be integrally closed; a curve model `Meta` over the algebraic closure of $\mathbb{Q}$ with function field `modularFunctionFieldBar (N₀ * q)`, an isomorphism `eeta` of its curve with the base change of `toBase N₀ q` to $\overline{\mathbb{Q}}$ compatible with the two structural morphisms, a Galois-equivariance condition `hgal` for the induced bijection between $\overline{\mathbb{Q}}$-points and places, and a pinning condition identifying the functions coming from `chartAlgFin (N₀ * q) q` with their $q$-expansions under `coeffEmb`; smoothness of relative dimension $1$ and geometric integrality of the generic fibre; the sections `εzero`, `εinf` over the base; and further data, among them a morphism $\pi$ with underlying scheme morphism `𝔓.π.1`. The conclusion is that `𝔓.π.1` is a finite morphism and is locally of finite presentation.
--
--   This is the finiteness half of the classical assertion that the degeneracy (forgetful) morphism from the Deligne–Rapoport model of $X_0(N_0 q)$ to that of $X_0(N_0)$ over $\mathbb{Z}_{(q)}$ is finite locally free of rank $q+1$. It is used by [`ModularCurve.DRModelPackageLevel.flat_pi`](thm.html#ModularCurve.DRModelPackageLevel.flat_pi) and by [`ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_pi`](thm.html#ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_pi), where flatness and the rank are supplied separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isFinite_and_locallyOfFinitePresentation_pi.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
namespace ModularCurve.DRModelPackageLevel

theorem isFinite_and_locallyOfFinitePresentation_pi (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) :
    IsFinite 𝔓.π.1 ∧ LocallyOfFinitePresentation 𝔓.π.1 := by sorry
