-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id
-- name    : ModularCurve.DRLevel.range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/404c8e6c-aa53-5872-8b30-ba35eee4f93e
-- title:
--   Reduction of the cusp ∞ meets only the first component
-- statement:
--   Fix $N_0\ge 1$ and a prime $q$ with $q\nmid N_0$, and write $R=$ `DRLevel.R q` for the coefficient ring over which the Igusa chart algebras are formed; `DRLevel.toBase N₀ q` and `DRLevel.toBase0 N₀ q` denote the structure morphisms `IgusaScheme.igusaTo (N₀ * q) q` and `IgusaScheme.igusaTo N₀ q` to $\operatorname{Spec} R$. The data are: a section $\varepsilon_\infty$ of `DRLevel.toBase N₀ q` over the identity of $\operatorname{Spec} R$, an $R$-algebra map $\rho_\infty$ from `IgusaScheme.chartAlgInf (N₀ * q) q` (the elements of the full modular function field of level $N_0q$ that are integral over $R[j^{-1}]$) to $R$ whose values are, rationally, the degree-zero Laurent coefficients of their arguments, and the hypothesis that the morphism underlying $\varepsilon_\infty$ is $\operatorname{Spec}\rho_\infty$ followed by the pole-chart inclusion `IgusaScheme.ιInf (N₀ * q) q`; a morphism $\pi$ from the level-$N_0q$ to the level-$N_0$ Igusa scheme commuting with the structure morphisms, pinned on the finite chart by an $R$-algebra map $\iota_0$ between the algebras `IgusaScheme.chartAlgFin` and on the pole chart by $\iota_\infty$ between the algebras `IgusaScheme.chartAlgInf`, each compatible with the Laurent expansions and intertwining the chart inclusions with $\pi$; an algebraically closed field $\kappa$ of characteristic $q$ with decidable equality and a ring map $\mathrm{to}\kappa : R\to\kappa$, giving the fibres `DRLevel.fibre toκ` and `DRLevel.fibre0 toκ` as pullbacks of the two structure morphisms along $\operatorname{Spec}(\mathrm{to}\kappa)$; and two morphisms $c_0,c_1$ from `DRLevel.fibre0 toκ` to `DRLevel.fibre toκ` over $\operatorname{Spec}\kappa$, both closed immersions, with $c_0$ a section of the morphism `DRLevel.fibreMap0 π toκ` induced by $\pi$, such that every point of `DRLevel.fibre toκ` lies in the image of $c_0$ or of $c_1$. The conclusion is that the image of the $\kappa$-point `DRLevel.sectionFibre εinf toκ` of `DRLevel.fibre toκ`, obtained from $\varepsilon_\infty$ by base change, is contained in the image of $c_0$ on points.
--
--   This is the statement that the cusp $\infty$ of the level-$N_0q$ model specialises, in the fibre at $q$, onto the component on which the forgetful morphism to level $N_0$ is the identity — the branch carrying the $q$-expansion — as in the Deligne–Rapoport description of the special fibre. It is used in the treatment of the reduction of the cusps, feeding [`ModularCurve.DRLevel.range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective`](thm.html#ModularCurve.DRLevel.range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicCurve
open ModularCurve ModularCurve.DRLevel
open ModularCurve.IgusaScheme

theorem ModularCurve.DRLevel.range_sectionFibre_epsInf_subset_range_of_comp_fibreMap0_eq_id
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase N₀ q))
    (rhoInf : ↥(IgusaScheme.chartAlgInf (N₀ * q) q) →ₐ[DRLevel.R q] DRLevel.R q)
    (hrho : ∀ b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q),
      ((rhoInf b : DRLevel.R q) : ℚ) = ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ).coeff 0)
    (hεchart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ IgusaScheme.ιInf (N₀ * q) q)

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

    (comp0 : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ)
    (hcomp_over : comp0 ≫ pullback.snd _ _ = pullback.snd _ _)
    [hcomp_ci : IsClosedImmersion comp0]
    (hcomp_pi : comp0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _)

    (comp1 : DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ)
    (hcomp1_over : comp1 ≫ pullback.snd _ _ = pullback.snd _ _)
    [hcomp1_ci : IsClosedImmersion comp1]
    (hjoint : ∀ y : DRLevel.fibre (N₀ := N₀) toκ, y ∈ Set.range comp0.base ∨ y ∈ Set.range comp1.base) :
    Set.range (DRLevel.sectionFibre εinf toκ).base ⊆ Set.range comp0.base := by sorry
