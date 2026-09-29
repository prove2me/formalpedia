-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_fst_pullback_comp_mem_range_iotaFin
-- name    : ModularCurve.DRLevel.fst_pullback_comp_mem_range_iotaFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/477450ef-9d1a-58f4-bd6d-aa4f917240f6
-- title:
--   Crossings of the mod q fibre avoid the cusps
-- statement:
--   Fix $N_0 \ge 1$ (nonzero) and a prime $q$ with $q \nmid N_0$, and write $R$ for the base ring `DRLevel.R q`. The data are: an isomorphism $w$ of the Igusa scheme `DRLevel.X N₀ q` with itself commuting with its structure morphism `DRLevel.toBase N₀ q = IgusaScheme.igusaTo (N₀ * q) q` to $\operatorname{Spec} R$; an $R$-algebra automorphism $\theta$ of the $j$-finite chart algebra `IgusaScheme.chartAlgFin (N₀ * q) q` (the subalgebra of `modularFunctionFieldFull (N₀ * q)` generated over the localised base by the $j$-function) which on elements coincides with `atkinLehnerInvolutionFull N₀ q`, together with the compatibility that `IgusaScheme.ιFin (N₀ * q) q` followed by $w$ equals $\operatorname{Spec}(\theta)$ followed by `IgusaScheme.ιFin (N₀ * q) q`; a morphism $\pi \colon$ `DRLevel.X N₀ q` $\to$ `DRLevel.X0 N₀ q` over $\operatorname{Spec} R$ (i.e. $\pi$ followed by `DRLevel.toBase0 N₀ q` is `DRLevel.toBase N₀ q`); an $R$-algebra map $\iota_0$ from `IgusaScheme.chartAlgFin N₀ q` to `IgusaScheme.chartAlgFin (N₀ * q) q` which is the identity on Laurent-series expansions over $\mathbf{Q}$, again compatible with the two $j$-finite chart immersions and $\pi$; an algebraically closed field $\kappa$ of characteristic $q$ with decidable equality and a ring map $R \to \kappa$. Finally, $\mathrm{comp} \colon \mathrm{Fin}\,2 \to (\mathrm{fibre0} \to \mathrm{fibre})$ gives two morphisms from the fibre `fibre0` $=$ `X0 N₀ q` $\times_{\operatorname{Spec} R} \operatorname{Spec} \kappa$ to the fibre `fibre` $=$ `X N₀ q` $\times_{\operatorname{Spec} R} \operatorname{Spec} \kappa$, each commuting with the projections to $\operatorname{Spec} \kappa$ and each a closed immersion, such that $\mathrm{comp}\,0$ followed by the fibre map induced by $\pi$ is the identity and $\mathrm{comp}\,0$ followed by the fibre map induced by $w$ is $\mathrm{comp}\,1$. The conclusion: every point $n$ of the fibre product of $\mathrm{comp}\,0$ and $\mathrm{comp}\,1$ has its image under the first projection to `fibre0`, followed by the projection to `X0 N₀ q`, in the range on points of the $j$-finite chart morphism `IgusaScheme.ιFin N₀ q`.
--
--   This is the statement that the two components of the reduction of $X_0(N_0q)$ modulo $q$ — two copies of $X_0(N_0)_{\kappa}$, interchanged by the Atkin–Lehner involution and each a section of the degeneracy map — meet only at points lying in the affine $j$-finite chart, so that no crossing point is a cusp; classically the cusps lie in the ordinary (Tate curve) locus, where the special fibre is smooth. It feeds the identification of the crossing points with supersingular places in [`ModularCurve.DRLevel.exists_nodeEquiv_placeOfPoint_eq`](thm.html#ModularCurve.DRLevel.exists_nodeEquiv_placeOfPoint_eq) and the reducedness statement [`ModularCurve.DRLevel.isReduced_pullback_comp`](thm.html#ModularCurve.DRLevel.isReduced_pullback_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_fst_pullback_comp_mem_range_iotaFin.lean

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

theorem ModularCurve.DRLevel.fst_pullback_comp_mem_range_iotaFin
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
    ∀ n : ↥(pullback (comp 0) (comp 1)),
      (pullback.fst (comp 0) (comp 1) ≫
          pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base n ∈
        Set.range (IgusaScheme.ιFin N₀ q).base := by sorry
