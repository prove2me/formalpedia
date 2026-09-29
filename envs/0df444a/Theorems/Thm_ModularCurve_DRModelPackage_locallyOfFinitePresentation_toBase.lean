-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase
-- name    : ModularCurve.DRModelPackage.locallyOfFinitePresentation_toBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/054d7b63-3d51-5b5b-ab32-5b7fe8d66a9a
-- title:
--   Finite presentation of the Deligne–Rapoport model over ℤ
-- statement:
--   Let $p$ be a prime and let $\mathfrak{X}$ be a term of the structure `DRModelPackage p`. Here `DRModel p` is the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel ℤ F (IgusaScheme.jFull p)`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), where $F$ is the intermediate field `modularFunctionFieldFull p` of $\mathbb{Q} \subset \mathbb{Q}((q))$ and `IgusaScheme.jFull p` is the element $j$ of $F$; by definition this scheme is the pushout of the two glueing morphisms attached to the subalgebras `chartAlgFin` $=$ `chartAlg ℤ F {j}` and `chartAlgInf` $=$ `chartAlg ℤ F {j⁻¹}` of $F$, and `DRModel.toBase p` is the morphism to $\operatorname{Spec}\mathbb{Z}$ obtained by descending the two structure morphisms $\operatorname{Spec}(\text{chartAlgFin}) \to \operatorname{Spec}\mathbb{Z}$ and $\operatorname{Spec}(\text{chartAlgInf}) \to \operatorname{Spec}\mathbb{Z}$ along the pushout. The hypothesis $\mathfrak{X}$ is the package whose fields record that `DRModel.toBase p` is proper and flat, that `DRModel p` is integral, that the sections over affine opens are integrally closed, identifications of the fibres over $\mathbb{Q}$ and over $\overline{\mathbb{Q}}$ with curve models together with the Galois and place compatibilities, two sections $\varepsilon_{\mathrm{zero}}, \varepsilon_{\mathrm{inf}}$ of the structure morphism over $\operatorname{Spec}\mathbb{Z}$, a maximal relative-dimension-one smooth open locus, and, in particular, the fields `chartFin_finite` and `chartInf_finite` asserting that the two chart algebras are finite modules over $\mathbb{Z}[X]$ via the maps `polynomialToChartFin` and `polynomialToChartInf`. The conclusion is that `DRModel.toBase p` is locally of finite presentation.
--
--   This is the finite-presentation property of the structure morphism of the Deligne–Rapoport integral model of the modular curve over $\operatorname{Spec}\mathbb{Z}$; over the Noetherian base $\mathbb{Z}$ it is equivalent to being locally of finite type. It is used as a standing input by later results about this model, among them the computation of branch ideals at the two sections, the construction of a resolved model package with its charts, and the integral closedness of the stalks of base changes of `DRModel.toBase p`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModelPackage.locallyOfFinitePresentation_toBase (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) :
    LocallyOfFinitePresentation (DRModel.toBase p) := by sorry
