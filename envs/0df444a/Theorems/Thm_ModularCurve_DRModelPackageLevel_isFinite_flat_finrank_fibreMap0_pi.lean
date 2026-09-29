-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isFinite_flat_finrank_fibreMap0_pi
-- name    : ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_fibreMap0_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/dc61c558-52e6-5965-9d8f-77915f53f6e3
-- title:
--   Fibrewise finiteness and rank q+1 of π
-- statement:
--   Fix natural numbers $N₀$ and $q$ with $N₀$ nonzero and $q$ prime, and assume $q \nmid N₀$. Let $\mathfrak P$ be a term of `DRModelPackageLevel N₀ q hqN`; among its data is a morphism $\mathfrak P.\pi$ over the base, that is, a morphism $\pi \colon$ `X N₀ q` $\to$ `X0 N₀ q` together with the identity $\pi$ followed by `toBase0 N₀ q` $=$ `toBase N₀ q`, where `toBase N₀ q` is `IgusaScheme.igusaTo (N₀ * q) q` and `toBase0 N₀ q` is `IgusaScheme.igusaTo N₀ q`, both morphisms to $\mathrm{Spec}$ of the base ring `DRLevel.R q`. Let $\kappa$ be a field and $\mathrm{to}\kappa \colon$ `DRLevel.R q` $\to \kappa$ a ring homomorphism. Consider `DRLevel.fibreMap0 𝔓.π toκ`, the morphism $\pi \times \mathrm{id}$ obtained by base change along $\mathrm{Spec}\,\kappa \to \mathrm{Spec}\,$`DRLevel.R q`, from the pullback of `toBase N₀ q` along that map to the pullback of `toBase0 N₀ q` along it. The assertion is that this morphism carries instances of `IsFinite` and `LocallyOfFinitePresentation`, is flat, and satisfies `finrank y = q + 1` at every point $y$ of its target.
--
--   This is the fibrewise form of the statement that the forgetful morphism between the Deligne–Rapoport type models of level $N₀q$ and level $N₀$ is finite locally free of degree $q+1$ away from $q \mid N₀$; stating it for an arbitrary field under the base ring covers both the generic fibre and the fibres in characteristic $q$. It is used in [`ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_comp_one_pi`](thm.html#ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_comp_one_pi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isFinite_flat_finrank_fibreMap0_pi.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
namespace ModularCurve.DRModelPackageLevel

theorem isFinite_flat_finrank_fibreMap0_pi (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) (κ : Type) [Field κ] (toκ : DRLevel.R q →+* κ) :
    ∃ (_ : IsFinite (DRLevel.fibreMap0 𝔓.π toκ)) (_ : LocallyOfFinitePresentation (DRLevel.fibreMap0 𝔓.π toκ)),
      Flat (DRLevel.fibreMap0 𝔓.π toκ) ∧ ∀ y, (DRLevel.fibreMap0 𝔓.π toκ).finrank y = q + 1 := by sorry
