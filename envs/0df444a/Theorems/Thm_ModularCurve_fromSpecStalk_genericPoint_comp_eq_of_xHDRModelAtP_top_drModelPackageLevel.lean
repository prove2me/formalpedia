-- Prove2me | Theorems.Thm_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel
-- name    : ModularCurve.fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/a294f259-da07-5d37-b87d-2870fb320e68
-- title:
--   Generic-point comparison of the two pinned curve models at level N₀p
-- statement:
--   Let $N_0\ge 1$, let $p$ be a prime with $p\nmid N_0$, put $M=N_0p$, and let $hpM$ witness $p\mid M$; let $h_j$ witness that the Laurent series `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by quotients of integral $q$-expansions of modular forms for $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be an `XHDRModelAtP` datum for $p$, level $M$ and $H=\top$, and $\mathfrak{P}$ a `DRModelPackageLevel` datum for $(N_0,p)$; each carries an integral proper flat normal model over $\mathbb{Z}_{(p)}$ built from the two $j$-charts, a `CurveModel` `Meta` over $\overline{\mathbb{Q}}$ (a smooth proper integral curve with a fixed isomorphism `ffEquiv` of its function field with `xHFunctionFieldBar M ⊤`, respectively `modularFunctionFieldBar M`, inside $\overline{\mathbb{Q}}((q))$), and an isomorphism `eeta` of `Meta.C` with the base change of the model to $\overline{\mathbb{Q}}$. Assume: $hF$, these two intermediate fields of $\overline{\mathbb{Q}}((q))$ are equal; $e$, an isomorphism between the Igusa two-chart model `IgusaScheme M p` and `XHDRLevel.X p (XHDRLevel.ΓM M ⊤) hj`, with $hbase$ saying that $e$.hom followed by the structure morphism to $\operatorname{Spec}\mathbb{Z}_{(p)}$ is `IgusaScheme.igusaTo M p`; $e_{\mathrm{Fin}}$, a ring homomorphism from the Igusa finite-chart algebra (the integral closure of $\mathbb{Z}_{(p)}[j]$ in `modularFunctionFieldFull M`) to the corresponding finite-chart algebra of the other model, which preserves $q$-expansions as Laurent series over $\mathbb{Q}$ ($hFin$) and whose Spec, followed by `IgusaScheme.ιFin M p`, equals `XHDRLevel.ιFin` followed by $e$.inv ($hcFin$); and $\psi:\mathfrak{X}.\mathrm{Meta}.C\to\mathfrak{P}.\mathrm{Meta}.C$ with $\psi$ followed by $\mathfrak{P}.\mathtt{eeta}$ and the first pullback projection equal to $\mathfrak{X}.\mathtt{eeta}$ followed by the first projection and $e$.inv ($h\psi_1$), and $\psi$ a morphism over $\operatorname{Spec}\overline{\mathbb{Q}}$ ($h\psi_2$). The conclusion is that the canonical morphism from $\operatorname{Spec}$ of the stalk at the generic point of $\mathfrak{X}.\mathrm{Meta}.C$, followed by $\psi$, equals $\operatorname{Spec}$ of the ring homomorphism obtained by composing $\mathfrak{P}.\mathrm{Meta}.\mathtt{ffEquiv}^{-1}$, the inverse of the identification of the two function fields provided by $hF$, and $\mathfrak{X}.\mathrm{Meta}.\mathtt{ffEquiv}$, followed by the canonical morphism from $\operatorname{Spec}$ of the stalk at the generic point of $\mathfrak{P}.\mathrm{Meta}.C$.
--
--   The statement says that, restricted to generic points, the comparison morphism $\psi$ between the two $q$-expansion-pinned geometric models is exactly the map induced by the identity of $q$-expansion function fields read through the two `ffEquiv` identifications. It serves as the generic-point input to the place-transport rigidity argument and is cited by [`ModularCurve.exists_iso_xHDRLevel_top_drLevel_epsInf_pointEquivPlace`](thm.html#ModularCurve.exists_iso_xHDRLevel_top_drLevel_epsInf_pointEquivPlace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.fromSpecStalk_genericPoint_comp_eq_of_xHDRModelAtP_top_drModelPackageLevel
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) [NeZero (N₀ * p)]
    (hpM : p ∣ N₀ * p) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p (N₀ * p) ⊤ hpM hj) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (hF : xHFunctionFieldBar (N₀ * p) ⊤ = modularFunctionFieldBar (N₀ * p))
    (e : IgusaScheme (N₀ * p) p ≅ XHDRLevel.X p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)
    (eFin : ↥(IgusaScheme.chartAlgFin (N₀ * p) p) →+* ↥(XHDRLevel.chartAlgFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj))
    (hFin : ∀ x : ↥(IgusaScheme.chartAlgFin (N₀ * p) p),
      (((eFin x : ↥(XHDRLevel.chartAlgFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj)) : ↥(qExpFunctionFieldC ℚ (XHDRLevel.ΓM (N₀ * p) ⊤))) :
          LaurentSeries ℚ) = ((x : ↥(modularFunctionFieldFull (N₀ * p))) : LaurentSeries ℚ))
    (hbase : e.hom ≫ XHDRLevel.toBase p (XHDRLevel.ΓM (N₀ * p) ⊤) hj = IgusaScheme.igusaTo (N₀ * p) p)
    (hcFin : Spec.map (CommRingCat.ofHom eFin) ≫ IgusaScheme.ιFin (N₀ * p) p = XHDRLevel.ιFin p (XHDRLevel.ΓM (N₀ * p) ⊤) hj ≫ e.inv)
    (ψ : 𝔛.Meta.C ⟶ 𝔓.Meta.C)
    (hψ₁ : ψ ≫ 𝔓.eeta ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ ≫ e.inv)
    (hψ₂ : ψ ≫ 𝔓.Meta.toBase = 𝔛.Meta.toBase) :
    𝔛.Meta.C.fromSpecStalk (genericPoint 𝔛.Meta.C) ≫ ψ =
      Spec.map (CommRingCat.ofHom
        (𝔛.Meta.ffEquiv.toRingHom.comp
          ((IntermediateField.equivOfEq hF).toRingEquiv.symm.toRingHom.comp 𝔓.Meta.ffEquiv.symm.toRingHom))) ≫
        𝔓.Meta.C.fromSpecStalk (genericPoint 𝔓.Meta.C) := by sorry
