-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective
-- name    : ModularCurve.DRLevel.range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/14b38cad-2aae-50e0-95b7-3b1fd20916ca
-- title:
--   Reduction of the cusps ∞ and 0 onto the two components
-- statement:
--   Let $N_0$ be a nonzero natural number and $q$ a prime with $q \nmid N_0$, let $R_q$ be the base ring of the level package and let $\mathfrak{X} =$ `DRLevel.X N₀ q` be the Igusa scheme of level $N_0q$ with structure morphism `toBase N₀ q` to $\operatorname{Spec} R_q$, and $\mathfrak{X}_0 =$ `DRLevel.X0 N₀ q` with structure morphism `toBase0 N₀ q`. The data are: two sections $\varepsilon_\infty, \varepsilon_0$ of `toBase N₀ q`, i.e. morphisms $\operatorname{Spec} R_q \to \mathfrak{X}$ whose composite with the structure morphism is the identity; an $R_q$-algebra map $\rho_\infty$ from the chart algebra `chartAlgInf (N₀ * q) q` to $R_q$ which, read in $\mathbb{Q}$, sends each element to the coefficient of $q^0$ of its Laurent expansion, together with the pinning $\varepsilon_\infty = \operatorname{Spec}(\rho_\infty)$ followed by the chart immersion `ιInf (N₀ * q) q`; an automorphism $w$ of $\mathfrak{X}$ over $\operatorname{Spec} R_q$, an $R_q$-algebra automorphism $\theta$ of `chartAlgFin (N₀ * q) q` inducing `atkinLehnerInvolutionFull N₀ q` on `modularFunctionFieldFull (N₀ * q)`, the compatibility that `ιFin (N₀ * q) q` followed by $w$ equals $\operatorname{Spec}(\theta)$ followed by `ιFin (N₀ * q) q`, and $\varepsilon_\infty$ followed by $w$ equal to $\varepsilon_0$; a morphism $\pi : \mathfrak{X} \to \mathfrak{X}_0$ over $\operatorname{Spec} R_q$, pinned on both charts by $R_q$-algebra maps $\iota_0$ and $\iota_\infty$ from the level-$N_0$ chart algebras to the level-$N_0q$ ones which are the identity on Laurent expansions. Let $\kappa$ be an algebraically closed field of characteristic $q$ with a ring map $R_q \to \kappa$, and write $\mathfrak{X}_\kappa$, $\mathfrak{X}_{0,\kappa}$ for the pullbacks `fibre` and `fibre0` along $\operatorname{Spec} \kappa \to \operatorname{Spec} R_q$. Finally let $c_0, c_1 : \mathfrak{X}_{0,\kappa} \to \mathfrak{X}_\kappa$ be morphisms over $\operatorname{Spec}\kappa$, each a closed immersion, whose images jointly contain every point of $\mathfrak{X}_\kappa$, with $c_0$ followed by the base change $\pi_\kappa$ of $\pi$ equal to the identity of $\mathfrak{X}_{0,\kappa}$ and $c_0$ followed by the base change $w_\kappa$ of $w$ equal to $c_1$. Writing $\infty_\kappa, 0_\kappa : \operatorname{Spec}\kappa \to \mathfrak{X}_\kappa$ for the $\kappa$-points obtained from $\varepsilon_\infty, \varepsilon_0$ by `sectionFibre`, the conclusion is the conjunction of four assertions: the image of $\infty_\kappa$ lies in the image of $c_0$ on points, the image of $0_\kappa$ lies in the image of $c_1$, and $\infty_\kappa$ followed by $\pi_\kappa$ and then by $c_0$, respectively by $c_1$, equals $\infty_\kappa$, respectively $0_\kappa$.
--
--   This is the statement that, on the Deligne–Rapoport model of $X_0(N_0q)$ in characteristic $q$, the cusp $\infty$ specialises onto the component on which the forgetful morphism to $X_0(N_0)$ is an isomorphism and the cusp $0 = w_q\infty$ onto the other, in the morphism-level form used by the later relative-Picard constructions. It is one of the inputs to [`ModularCurve.nonempty_dRModelPackageLevel`](thm.html#ModularCurve.nonempty_dRModelPackageLevel), which assembles the full level package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve
open ModularCurve.IgusaScheme
open ModularCurve.DRLevel

theorem ModularCurve.DRLevel.range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (εinf εzero : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase N₀ q))
    (rhoInf : ↥(IgusaScheme.chartAlgInf (N₀ * q) q) →ₐ[DRLevel.R q] DRLevel.R q)
    (hrho : ∀ b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q),
      ((rhoInf b : DRLevel.R q) : ℚ) = ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ).coeff 0)
    (hεchart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ IgusaScheme.ιInf (N₀ * q) q)

    (w : DRLevel.X N₀ q ≅ DRLevel.X N₀ q) (hw : w.hom ≫ DRLevel.toBase N₀ q = DRLevel.toBase N₀ q)
    (theta : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ≃ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (htheta : ∀ b, ((theta b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) =
      atkinLehnerInvolutionFull N₀ q (b : ↥(modularFunctionFieldFull (N₀ * q))))
    (hwchart : IgusaScheme.ιFin (N₀ * q) q ≫ w.hom =
      Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hws : εinf.1 ≫ w.hom = εzero.1)

    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)

    (iotaInf : ↥(IgusaScheme.chartAlgInf N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgInf (N₀ * q) q))
    (hiotaInf : ∀ b, (((iotaInf b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichartInf : IgusaScheme.ιInf (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ IgusaScheme.ιInf N₀ q)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_surj : ∀ y : DRLevel.fibre (N₀ := N₀) toκ, y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base)
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw toκ = comp 1) :
    Set.range (DRLevel.sectionFibre εinf toκ).base ⊆ Set.range (comp 0).base ∧
    Set.range (DRLevel.sectionFibre εzero toκ).base ⊆ Set.range (comp 1).base ∧
    (DRLevel.sectionFibre εinf toκ ≫ DRLevel.fibreMap0 π toκ) ≫ comp 0 = DRLevel.sectionFibre εinf toκ ∧
    (DRLevel.sectionFibre εinf toκ ≫ DRLevel.fibreMap0 π toκ) ≫ comp 1 = DRLevel.sectionFibre εzero toκ := by sorry
