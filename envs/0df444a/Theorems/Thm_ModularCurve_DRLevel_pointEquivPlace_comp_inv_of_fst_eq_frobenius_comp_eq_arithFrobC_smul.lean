-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul
-- name    : ModularCurve.DRLevel.pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/8b8ee491-9f5e-5044-aeb6-0a0e83366f13
-- title:
--   Frobenius twisting of κ-points translates places by arithmetic Frobenius
-- statement:
--   Fix $N_0 \ne 0$ and a prime $q$ with $q \nmid N_0$, an algebraically closed field $\kappa$ of characteristic $q$, and a ring homomorphism $\mathrm{to}\kappa$ from the coefficient ring `DRLevel.R q` to $\kappa$. Let $M$ be a `CurveModel` for $\kappa$ and the field $\mathrm{modularFunctionFieldC}\,\kappa\,N_0 = \kappa(\,j, j(N_0\cdot)\,) \subset \kappa((q))$, i.e. an integral scheme $M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\kappa$, with a $\kappa$-compatible isomorphism `ffEquiv` onto its function field and a bijection `placeOfPoint` from closed points to places matching stalks with valuation rings. Let $e : M.C \to \mathrm{fibre0}\,\mathrm{to}\kappa = X_0(N_0)_{R_q} \times_{\operatorname{Spec} R_q} \operatorname{Spec}\kappa$ be an isomorphism with $e$ followed by the second projection equal to $M.toBase$; assume the preimage under $e$ followed by the first projection of the open image of the finite chart $\iota_{\mathrm{Fin}}$ is nonempty, and assume the pinning hypothesis: for each $b$ in the chart algebra $\mathrm{chartAlgFin}\,N_0\,q$, the element of $\mathrm{modularFunctionFieldC}\,\kappa\,N_0$ obtained by pulling $b$ back along that map, taking its germ at the generic point and transporting by `ffEquiv`$^{-1}$, equals $\mathrm{jGeomGen}\,\kappa\,N_0$ when $b = \mathrm{jChartFin}\,N_0\,q$, and equals $\mathrm{jNGeomGen}\,\kappa\,N_0$ when the Laurent series over $\mathbb{Q}$ underlying $b$ is $\mathrm{qExpand}\,\mathbb{Q}\,N_0\,j$. Finally let $x, y : \operatorname{Spec}\kappa \to \mathrm{fibre0}$ be sections of the second projection such that $y$ followed by the first projection equals $\operatorname{Spec}$ of the $q$-power Frobenius of $\kappa$ followed by $x$ followed by the first projection. Then the place of $\mathrm{modularFunctionFieldC}\,\kappa\,N_0$ over $\kappa$ attached by `pointEquivPlace` to the $\kappa$-point $y \circ e^{-1}$ is the translate, under the action of the semilinear automorphism $\mathrm{arithFrobC}\,q\,\kappa\,N_0$ (coefficientwise $q$-power map together with the $q$-power automorphism of $\kappa$), of the place attached to $x \circ e^{-1}$.
--
--   This is the compatibility, in the level-$N_0$ special-fibre dictionary, between Frobenius twisting of geometric points of $X_0(N_0)_\kappa$ and the arithmetic Frobenius action on places of the geometric modular function field. It is used by [`ModularCurve.JZeroNeronObjectAtP.LevelModel.fibrePt_eq_fibrePt_comp_frobenius_of_isFrobeniusAt`](thm.html#ModularCurve.JZeroNeronObjectAtP.LevelModel.fibrePt_eq_fibrePt_comp_frobenius_of_isFrobeniusAt) in the identification of Frobenius-fixed points in the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem ModularCurve.DRLevel.pointEquivPlace_comp_inv_of_fst_eq_frobenius_comp_eq_arithFrobC_smul
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

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

    (x : Spec (CommRingCat.of κ) ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) (hx : x ≫ pullback.snd _ _ = 𝟙 _)
    (y : Spec (CommRingCat.of κ) ⟶ DRLevel.fibre0 (N₀ := N₀) toκ) (hy : y ≫ pullback.snd _ _ = 𝟙 _)
    (hyx : y ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (frobenius κ q)) ≫ x ≫ pullback.fst _ _) :
    M.pointEquivPlace ⟨y ≫ inv e, by rw [Category.assoc, ← heM, IsIso.inv_hom_id_assoc, hy]⟩ =
      arithFrobC q κ N₀ • M.pointEquivPlace ⟨x ≫ inv e, by rw [Category.assoc, ← heM, IsIso.inv_hom_id_assoc, hx]⟩ := by sorry
