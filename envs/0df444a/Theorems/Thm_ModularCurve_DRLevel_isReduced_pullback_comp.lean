-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_isReduced_pullback_comp
-- name    : ModularCurve.DRLevel.isReduced_pullback_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/2a595791-93fe-5ab0-b9ab-2cd102b03c66
-- title:
--   Reduced intersection of the two fibre components at q
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$, and work over the ring `DRLevel.R q`, writing `DRLevel.X N₀ q` and `DRLevel.X0 N₀ q` for the Igusa schemes of levels $N_0q$ and $N_0$ with their structure morphisms `DRLevel.toBase N₀ q` $=$ `IgusaScheme.igusaTo (N₀ * q) q` and `DRLevel.toBase0 N₀ q` $=$ `IgusaScheme.igusaTo N₀ q` to $\operatorname{Spec}$ of `DRLevel.R q`. The data are: a self-isomorphism $w$ of `DRLevel.X N₀ q` over the base ($w.\mathrm{hom}$ followed by `toBase` is `toBase`); an `R q`-algebra automorphism $\theta$ of the finite chart algebra $\mathrm{chartAlgFin}(N_0q,q)$ which on the modular function field $\mathrm{modularFunctionFieldFull}(N_0q)$ induces `atkinLehnerInvolutionFull N₀ q`, together with the compatibility that the chart immersion `ιFin (N₀ * q) q` followed by $w.\mathrm{hom}$ equals $\operatorname{Spec}(\theta)$ followed by that same immersion; a morphism $\pi \colon$ `X N₀ q` $\to$ `X0 N₀ q` over the base; an `R q`-algebra map $\iota_0$ from $\mathrm{chartAlgFin}(N_0,q)$ to $\mathrm{chartAlgFin}(N_0q,q)$ which is the identity on Laurent-series expansions, with the analogous chart compatibility for $\pi$; an algebraically closed field $\kappa$ of characteristic $q$ and a ring homomorphism $\mathrm{to}\kappa \colon$ `R q` $\to \kappa$, giving the fibres $\mathrm{fibre} =$ `X N₀ q` $\times_{\operatorname{Spec} R q} \operatorname{Spec} \kappa$ and $\mathrm{fibre}_0$ likewise for `X0 N₀ q`; finally two morphisms $c_0, c_1 \colon \mathrm{fibre}_0 \to \mathrm{fibre}$, each compatible with the projections to $\operatorname{Spec}\kappa$ and each a closed immersion, such that $c_0$ followed by the base change `fibreMap0 π toκ` of $\pi$ is the identity and $c_0$ followed by the base change `fibreMap w.hom hw toκ` of $w$ is $c_1$. The conclusion is that the fibre product of $c_0$ and $c_1$ is a reduced scheme.
--
--   This is the transversality statement for the Deligne–Rapoport model: in the fibre at $q$ of the modular curve of level $N_0q$ the two copies of the level-$N_0$ curve, the section of the degeneracy morphism and its Atkin–Lehner translate, meet in a scheme-theoretic intersection that is reduced (ordinary double points at the supersingular locus). It supplies the reducedness of the crossing in the construction of a level package, [`ModularCurve.nonempty_dRModelPackageLevel`](thm.html#ModularCurve.nonempty_dRModelPackageLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_isReduced_pullback_comp.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve.IgusaScheme ModularCurve.DRLevel
open ModularCurve

theorem ModularCurve.DRLevel.isReduced_pullback_comp
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

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw toκ = comp 1) :
    IsReduced (pullback (comp 0) (comp 1)) := by sorry
