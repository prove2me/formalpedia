-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_comp_zero
-- name    : ModularCurve.DRModelPackageLevel.mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_comp_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/491a3dc6-8b6c-5d95-a12d-b4200a570b8b
-- title:
--   Smoothness and ε_∞-component for points off the second component
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak P$ be a term of the structure `DRModelPackageLevel N₀ q hqN`, whose data include the scheme `DRLevel.X N₀ q` with its structure morphism `DRLevel.toBase N₀ q = IgusaScheme.igusaTo (N₀ * q) q` to $\operatorname{Spec}$ of the ring `DRLevel.R q` (proper, flat and locally of finite presentation, with integral source), an open `𝔓.smoothLocus` of `DRLevel.X N₀ q` which is smooth of relative dimension $1$ over the base and maximal among opens smooth over it, a section `𝔓.εinf` of `DRLevel.toBase N₀ q`, and, for each algebraically closed field $\kappa$ and ring homomorphism $\mathrm{to}\kappa$ from `DRLevel.R q` to $\kappa$, two morphisms `𝔓.comp κ toκ 0` and `𝔓.comp κ toκ 1` into the fibre `DRLevel.fibre toκ`, the pullback of `DRLevel.toBase N₀ q` along $\operatorname{Spec}(\mathrm{to}\kappa)$. Let $\kappa$ be an algebraically closed field of characteristic $q$, let $\mathrm{to}\kappa$ be as above, and let $y$ be a point of `DRLevel.fibre toκ` lying in the set-theoretic range of the underlying map of `𝔓.comp κ toκ 0` but not in that of `𝔓.comp κ toκ 1`. Then the image of $y$ under the first projection from the fibre to `DRLevel.X N₀ q` lies in `𝔓.smoothLocus`, and $y$ lies in the connected component, inside the open preimage of `𝔓.smoothLocus` in the fibre, of the point obtained by applying the section `DRLevel.sectionFibre 𝔓.εinf toκ` of the fibre over $\kappa$ (the lift of $\operatorname{Spec}(\mathrm{to}\kappa)$ followed by `𝔓.εinf` together with the identity) to the closed point of $\operatorname{Spec} \kappa$.
--
--   This is the fibre-by-fibre statement that, on the characteristic-$q$ fibre of the Deligne–Rapoport model of level $N_0q$, a point lying on the first of the two components and off the second is a smooth point and lies in the connected component of the cusp $\infty$ section. It is used in the construction of the degeneracy and pinning data for the special fibre and in the comparison of the cusp component with the finite-$j$ chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_comp_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped Polynomial

namespace ModularCurve.DRModelPackageLevel

theorem mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_comp_zero
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    (y : ↥(DRLevel.fibre (N₀ := N₀) toκ))
    (hy0 : y ∈ Set.range (𝔓.comp κ toκ 0).base) (hy1 : y ∉ Set.range (𝔓.comp κ toκ 1).base) :
    (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base y ∈ (𝔓.smoothLocus : Set ↥(DRLevel.X N₀ q)) ∧
    y ∈ connectedComponentIn ((pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)) ⁻¹ᵁ 𝔓.smoothLocus :
        (DRLevel.fibre (N₀ := N₀) toκ).Opens) : Set ↥(DRLevel.fibre (N₀ := N₀) toκ))
        ((DRLevel.sectionFibre 𝔓.εinf toκ).base (IsLocalRing.closedPoint κ)) := by sorry
