-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_epsInf_comp_pi_eq
-- name    : ModularCurve.DRModelPackageLevel.epsInf_comp_pi_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/8959b512-df8f-5458-84cd-2d547029ef8a
-- title:
--   Package cusp ∞ followed by π is the Igusa cusp
-- statement:
--   Fix $N_0\ge 1$ and a prime $q$ with $q\nmid N_0$, and let $\mathfrak P$ be an inhabitant of `DRModelPackageLevel N₀ q hqN`, the bundle of data and properties for the model `X N₀ q` over $\operatorname{Spec} R$, $R=$ `DRLevel.R q`, whose structure morphism is the Igusa morphism `igusaTo (N₀*q) q`; among its fields are the section `εinf` of that structure morphism and the morphism `π` over $\operatorname{Spec} R$ to `X0 N₀ q`, the Igusa scheme of level $N_0$ with structure morphism `igusaTo N₀ q`. Let $\varphi_\infty$ be an $R$-algebra homomorphism from `chartAlgInf N₀ q` to $R$, where `chartAlgInf N₀ q` is the subalgebra of elements of `modularFunctionFieldFull N₀` integral over the subalgebra generated over $R$ by $j^{-1}$, and assume that for every $x$ in that chart algebra the rational number underlying $\varphi_\infty(x)$ is the coefficient of degree $0$ of the Laurent ($q$-expansion) series of $x$. Let $\varepsilon_0$ be a section of `igusaTo N₀ q` over the identity of $\operatorname{Spec} R$ whose underlying morphism is $\operatorname{Spec}\varphi_\infty$ followed by the chart immersion `ιInf N₀ q`. Then the underlying morphism of `εinf` followed by that of `π` equals the underlying morphism of $\varepsilon_0$, as morphisms $\operatorname{Spec} R\to$ `X0 N₀ q`.
--
--   This is the compatibility of the two pins of the cusp $\infty$: the cusp section carried by the Deligne–Rapoport-style package at level $N_0q$, pushed along the degeneracy morphism $\pi$, is the cusp of the level-$N_0$ Igusa model cut out on the chart at infinity by the constant term of the $q$-expansion. It lets consumers, here [`ModularCurve.exists_jZeroNeronObjectAtP_and_bridge`](thm.html#ModularCurve.exists_jZeroNeronObjectAtP_and_bridge), transfer statements about the package's cusp to statements about the $q$-expansion-normalised cusp at level $N_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_epsInf_comp_pi_eq.lean

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

theorem epsInf_comp_pi_eq (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (φinf : ↥(IgusaScheme.chartAlgInf N₀ q) →ₐ[DRLevel.R q] DRLevel.R q)
    (hφinf : ∀ x : ↥(IgusaScheme.chartAlgInf N₀ q),
      ((φinf x : DRLevel.R q) : ℚ) = ((x : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ).coeff 0)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (DRLevel.R q)))) (DRLevel.toBase0 N₀ q))
    (hε₀ : ε₀.1 = Spec.map (CommRingCat.ofHom φinf.toRingHom) ≫ IgusaScheme.ιInf N₀ q) :
    𝔓.εinf.1 ≫ 𝔓.π.1 = ε₀.1 := by sorry
