-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul
-- name    : ModularCurve.DRLevel.placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/714e536b-de52-58a8-ae8e-59b6db142ae1
-- title:
--   Frobenius on places via the second component mod q
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$, and write $R=R_q$ for the base ring, $X = X(N_0,q)$ for the Igusa scheme of level $N_0q$ with its structure morphism `DRLevel.toBase` to $\operatorname{Spec} R$, and $X_0 = X(N_0,q)$ at level $N_0$ with structure morphism `DRLevel.toBase0`. The data are: an automorphism $w$ of $X$ over the base, an $R$-algebra automorphism $\theta$ of the chart algebra $\mathrm{chartAlgFin}(N_0q,q)$ which on underlying elements of $\mathrm{modularFunctionFieldFull}(N_0q)$ coincides with `atkinLehnerInvolutionFull` $N_0\,q$ (the chosen automorphism interchanging $\mathrm{qExpand}_{\mathbf Q}^{d}(j_q)$ and $\mathrm{qExpand}_{\mathbf Q}^{dq}(j_q)$ for all $d \mid N_0$, if such exists), together with the compatibility $\iota_{\mathrm{Fin}} \circ$-after-$w$ $=$ $\operatorname{Spec}\theta$ followed by $\iota_{\mathrm{Fin}}$; a morphism $\pi : X \to X_0$ over the base, an $R$-algebra map $\iota_0 : \mathrm{chartAlgFin}(N_0,q) \to \mathrm{chartAlgFin}(N_0q,q)$ preserving Laurent-series expansions, and the corresponding chart compatibility for $\pi$; an algebraically closed field $\kappa$ of characteristic $q$ and a ring homomorphism $\mathrm{to}\kappa : R \to \kappa$, so that `DRLevel.fibre` and `DRLevel.fibre0` are the fibres of $X$ and $X_0$ over this geometric point; a curve model $M$ over $\kappa$ with function field $\mathrm{modularFunctionFieldC}\,\kappa\,N_0 = \kappa(j_q\bmod, j_{q,N_0}\bmod)$ (an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\kappa$, with a bijection `placeOfPoint` from closed points to places matching stalks with valuation rings), an isomorphism $e$ from $M.C$ to `DRLevel.fibre0` over $\operatorname{Spec}\kappa$ whose chart preimage is nonempty and which is pinned, in the sense that for every $b$ in $\mathrm{chartAlgFin}(N_0,q)$ the element of the function field obtained by reading $b$ through the chart open of $\iota_{\mathrm{Fin}}(N_0,q)$ and transporting by $M.\mathrm{ffEquiv}^{-1}$ equals `jGeomGen` $\kappa\,N_0$ when $b$ is the chart generator `jChartFin`, and equals `jNGeomGen` $\kappa\,N_0$ when the Laurent expansion of $b$ is $\mathrm{qExpand}_{\mathbf Q}^{N_0}(j_q)$; finally two morphisms $\mathrm{comp}_0,\mathrm{comp}_1$ from `DRLevel.fibre0` to `DRLevel.fibre`, both over $\operatorname{Spec}\kappa$ and both closed immersions, with $\mathrm{comp}_0$ followed by `DRLevel.fibreMap0` $\pi$ the identity and $\mathrm{comp}_0$ followed by `DRLevel.fibreMap` $w$ equal to $\mathrm{comp}_1$. The conclusion: for every closed point $P$ of $M.C$, the image of $P$ under $e$, then $\mathrm{comp}_1$, then the fibre map induced by $\pi$, then $e^{-1}$, is again a closed point, and its place is the translate of the place of $P$ by `arithFrobC` $q\,\kappa\,N_0$, the semilinear automorphism of $\mathrm{modularFunctionFieldC}\,\kappa\,N_0$ given by applying the $q$-power Frobenius of $\kappa$ to Laurent coefficients.
--
--   This is the Deligne–Rapoport description of the special fibre of $X_0(N_0q)$ at $q$: of the two copies of $X_0(N_0)_\kappa$ sitting inside it, the forgetful map restricts to the identity on the first and to the $q$-power Frobenius on the second, here recorded as an identity between places of the function field. It supplies the corresponding field of the Deligne–Rapoport level package produced by [`ModularCurve.nonempty_dRModelPackageLevel`](thm.html#ModularCurve.nonempty_dRModelPackageLevel), from which the Eichler–Shimura relation and the Hecke action are read off.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul.lean

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

theorem ModularCurve.DRLevel.placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul
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

    (M : CurveModel κ ↥(modularFunctionFieldC κ N₀)) (e : M.C ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) [IsIso e]
    (heM : e ≫ pullback.snd _ _ = M.toBase)
    [hMne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ
      ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)))]
    (hMpin : ∀ b : ↥(IgusaScheme.chartAlgFin N₀ q),
        let readb : ↥(modularFunctionFieldC κ N₀) :=
          M.ffEquiv.symm
            (M.C.germToFunctionField
              ((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
              (((e ≫ pullback.fst (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
                (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv b))))
        ((b = IgusaScheme.jChartFin N₀ q → readb = jGeomGen κ N₀) ∧
          (((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ) = qExpand ℚ N₀ jq → readb = jNGeomGen κ N₀)))

    (comp : Fin 2 → (DRLevel.fibre0 (N₀ := N₀) toκ ⟶ DRLevel.fibre (N₀ := N₀) toκ))
    (hcomp_over : ∀ i, comp i ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcomp_ci : ∀ i, IsClosedImmersion (comp i))
    (hcomp_pi : comp 0 ≫ DRLevel.fibreMap0 π toκ = 𝟙 _)
    (hcomp_w : comp 0 ≫ DRLevel.fibreMap w.hom hw toκ = comp 1) :
    ∀ P : closedPoints M.C,
      ∃ h : (inv e).base ((e ≫ comp 1 ≫ DRLevel.fibreMap0 π toκ).base P.1) ∈ closedPoints M.C,
        M.placeOfPoint ⟨_, h⟩ = arithFrobC q κ N₀ • M.placeOfPoint P := by sorry
