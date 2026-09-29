-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_crossingPt_mem_preimage_chartFin
-- name    : ModularCurve.DRModelPackage.crossingPt_mem_preimage_chartFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/18a8298d-0abf-5c4a-8667-070e023fa169
-- title:
--   Crossings lie over the j-finite chart
-- statement:
--   Let $p$ be a prime with $5 \le p$, and let $\mathfrak X$ be a term of `DRModelPackage p`, so that in particular $\mathfrak X$ supplies the two morphisms $\mathfrak X.\mathrm{compInf}\,\kappa$ and $\mathfrak X.\mathrm{compZero}\,\kappa$ from the curve $(\mathfrak X.\mathrm{ratModel}\,\kappa).C$ into the base change $\mathrm{DRModel}(p) \times_{\operatorname{Spec}\mathbb Z} \operatorname{Spec}\kappa$, where $\mathrm{DRModel}(p)$ is the two-chart integral model `TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)` over $\mathbb Z$. Let $O$ be a commutative ring, $\kappa$ an algebraically closed field of characteristic $p$, and $\mathrm{to}\kappa : O \to \kappa$ a ring homomorphism. Let $n$ be a point of the scheme-theoretic fibre product of $\mathfrak X.\mathrm{compInf}\,\kappa$ and $\mathfrak X.\mathrm{compZero}\,\kappa$. The associated point $\mathfrak X.\mathrm{crossingPt}\,O\,\kappa\,\mathrm{to}\kappa\,n$ of $\mathrm{DRModel}(p) \times_{\operatorname{Spec}\mathbb Z} \operatorname{Spec} O$, namely the image of $n$ under the underlying map of the first projection followed by $\mathfrak X.\mathrm{compInf}\,\kappa$ followed by the base-change map along $\mathrm{to}\kappa$, is asserted to lie in the preimage, under the first projection to $\mathrm{DRModel}(p)$, of the open image of the whole of the $j$-finite chart under `TwoChartIntegralModel.ιFin`.
--
--   The statement says that the crossing points of the two components of the characteristic $p$ geometric fibre of the Deligne–Rapoport model of $X_0(p)$ lie over the chart where $j$ is finite (equivalently, the supersingular crossings are not cusps). It is used in the analysis of the local structure of the model at a crossing, in particular by the results producing local equations for the germ of the $j$-coordinate at a crossing and by the corresponding statements for the resolved model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_crossingPt_mem_preimage_chartFin.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModelPackage.crossingPt_mem_preimage_chartFin
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    𝔛.crossingPt O κ toκ n ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by sorry
