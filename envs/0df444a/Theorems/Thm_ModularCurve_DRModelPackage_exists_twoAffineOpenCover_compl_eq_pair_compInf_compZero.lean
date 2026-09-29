-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_twoAffineOpenCover_compl_eq_pair_compInf_compZero
-- name    : ModularCurve.DRModelPackage.exists_twoAffineOpenCover_compl_eq_pair_compInf_compZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/f550277d-c446-5151-b3bc-e01d0a275a40
-- title:
--   Two-affine cover of the bad fibre avoiding crossing points
-- statement:
--   Let $p$ be a prime, let $\mathfrak X$ be a Deligne–Rapoport package for $p$ (a `DRModelPackage p`, bundling properness, flatness, integrality and normality of the structure morphism `DRModel.toBase p` from the two-chart integral model $\operatorname{TwoChartIntegralModel}\,\mathbf Z\,\mathrm{modularFunctionFieldFull}\,p\,(\mathrm{jFull}\,p)$ to $\operatorname{Spec}\mathbf Z$, together with curve models over $\mathbf Q$ and over $\overline{\mathbf Q}$ identified with the corresponding fibres and compatible with places and the arithmetic Galois action, two sections $\varepsilon_\infty,\varepsilon_0$ of `DRModel.toBase p`, and a distinguished smooth-locus open), and let $\kappa$ be an algebraically closed field of characteristic $p$. Put $X=\operatorname{pullback}$ of `DRModel.toBase p` along $\operatorname{Spec}$ of $\mathbf Z\to\kappa$. The assertion is that there exist a `TwoAffineOpenCover` $\mathcal W_0$ of $X$, i.e. two opens $U_0,U_1$ that are affine, have affine intersection and satisfy $U_0\sqcup U_1=\top$, and four closed points $x_1,y_1,x_2,y_2$ of the scheme underlying $\mathfrak X.\mathrm{ratModel}\ \kappa$, such that, writing $C_\infty=\mathfrak X.\mathrm{compInf}\ \kappa$ and $C_0=\mathfrak X.\mathrm{compZero}\ \kappa$ for the two morphisms from that scheme to $X$: the image $C_\infty(x_1)$ is the image of the closed point of $\operatorname{Spec}\kappa$ under `DRModel.sectionFibre 𝔛.εinf (algebraMap ℤ κ)`, namely the $\kappa$-point of $X$ obtained from $\varepsilon_\infty$ by base change; the set-theoretic complements of $U_0$ and of $U_1$ in $X$ are exactly $\{C_\infty(x_1),C_0(x_2)\}$ and $\{C_\infty(y_1),C_0(y_2)\}$ respectively; and $C_\infty(x_1),C_\infty(y_1)$ lie outside the range of $C_0$ on points while $C_0(x_2),C_0(y_2)$ lie outside the range of $C_\infty$.
--
--   For the characteristic-$p$ geometric fibre of the Deligne–Rapoport model this produces a cover by two affine opens each of which omits exactly one point of each of the two components, these omitted points being away from the crossings, and with the reduction of the cusp $\infty$ among them. It feeds the degeneration hypothesis used in [`ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth`](thm.html#ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth) and its variant `exists_twoLineDegeneration_of_not_smooth_iso_comp_eq`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_twoAffineOpenCover_compl_eq_pair_compInf_compZero.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRModelPackage.exists_twoAffineOpenCover_compl_eq_pair_compInf_compZero
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] :
    ∃ (𝒲₀ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).TwoAffineOpenCover) (x₁ y₁ x₂ y₂ : closedPoints (𝔛.ratModel κ).C),
      (𝔛.compInf κ).base x₁.1 = (DRModel.sectionFibre 𝔛.εinf (algebraMap ℤ κ)).base (IsLocalRing.closedPoint κ) ∧
      ((𝒲₀.U0 : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))))ᶜ = {(𝔛.compInf κ).base x₁.1, (𝔛.compZero κ).base x₂.1} ∧
      ((𝒲₀.U1 : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))))ᶜ = {(𝔛.compInf κ).base y₁.1, (𝔛.compZero κ).base y₂.1} ∧
      (𝔛.compInf κ).base x₁.1 ∉ Set.range (𝔛.compZero κ).base ∧ (𝔛.compZero κ).base x₂.1 ∉ Set.range (𝔛.compInf κ).base ∧
      (𝔛.compInf κ).base y₁.1 ∉ Set.range (𝔛.compZero κ).base ∧ (𝔛.compZero κ).base y₂.1 ∉ Set.range (𝔛.compInf κ).base := by sorry
