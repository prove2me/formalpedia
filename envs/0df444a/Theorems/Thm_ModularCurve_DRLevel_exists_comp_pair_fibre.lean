-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_exists_comp_pair_fibre
-- name    : ModularCurve.DRLevel.exists_comp_pair_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/6b289654-4eec-594f-803e-0bd90d42363b
-- title:
--   Special fibre at q: two components with section and w_q-translate
-- statement:
--   Fix $N_0\ge 1$ and a prime $q$ with $q\nmid N_0$, and work over the base ring `DRLevel.R q`. The data are: an isomorphism $w$ of the scheme `DRLevel.X N₀ q` with itself whose underlying map commutes with the structure morphism `DRLevel.toBase N₀ q` $=$ `IgusaScheme.igusaTo (N₀ * q) q` to $\operatorname{Spec}$ of `DRLevel.R q`; an `DRLevel.R q`-algebra automorphism $\theta$ of the $j$-finite chart algebra `IgusaScheme.chartAlgFin (N₀ * q) q` which on elements of `modularFunctionFieldFull (N₀ * q)` agrees with `atkinLehnerInvolutionFull N₀ q`, together with the compatibility that `IgusaScheme.ιFin (N₀ * q) q` followed by $w$ equals $\operatorname{Spec}(\theta)$ followed by `IgusaScheme.ιFin (N₀ * q) q`; a morphism $\pi$ from `DRLevel.X N₀ q` to `DRLevel.X0 N₀ q` commuting with the two structure morphisms to $\operatorname{Spec}$ of `DRLevel.R q`; an `DRLevel.R q`-algebra map $\iota_0$ from `IgusaScheme.chartAlgFin N₀ q` to `IgusaScheme.chartAlgFin (N₀ * q) q` preserving Laurent-series expansions over $\mathbb{Q}$, with the analogous chart compatibility for $\pi$; and an algebraically closed field $\kappa$ of characteristic $q$ with a ring map $\mathrm{to}\kappa$ from `DRLevel.R q`. Writing $\mathfrak{X}_\kappa$ and $\mathfrak{X}_{0,\kappa}$ for the pullbacks of the two structure morphisms along $\operatorname{Spec}(\mathrm{to}\kappa)$, the conclusion is the existence of two morphisms $c_0,c_1\colon \mathfrak{X}_{0,\kappa}\to\mathfrak{X}_\kappa$, each compatible with the projections to $\operatorname{Spec}\kappa$, each a closed immersion, whose images together cover every point of $\mathfrak{X}_\kappa$ and are distinct as subsets, such that $c_0$ followed by the induced map `DRLevel.fibreMap0 π toκ` is the identity of $\mathfrak{X}_{0,\kappa}$ and $c_0$ followed by the induced map `DRLevel.fibreMap w.hom hw toκ` is $c_1$.
--
--   This is the scheme-theoretic form, for the two-chart Igusa model, of the Deligne–Rapoport description of the reduction modulo $q$ of $X_0(N_0q)$ as the union of two copies of $X_0(N_0)$, one a section of the forgetful morphism and the other its translate by the partial Atkin–Lehner involution $w_q$. It feeds into the construction of the Deligne–Rapoport model package at level $N_0q$ used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_exists_comp_pair_fibre.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.DRLevel
open ModularCurve.IgusaScheme

theorem ModularCurve.DRLevel.exists_comp_pair_fibre
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (htheta : ∀ b, ((theta b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
      atkinLehnerInvolutionFull N₀ q (b : ↥(modularFunctionFieldFull (N₀ * q))))
    (hwchart : IgusaScheme.ιFin (N₀ * q) q ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)

    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ) :
    ∃ comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ),
      (∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _) ∧
      (∀ i, IsClosedImmersion (comp i)) ∧
      (∀ y : DRLevel.fibre (N₀ := N₀) toκ, y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base) ∧
      Set.range (comp 0).base ≠ Set.range (comp 1).base ∧
      comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _ ∧
      comp 0 ≫ DRLevel.fibreMap w.hom hw toκ = comp 1 := by sorry
