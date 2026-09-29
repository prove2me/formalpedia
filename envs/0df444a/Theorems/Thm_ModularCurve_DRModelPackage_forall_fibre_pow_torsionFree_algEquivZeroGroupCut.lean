-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_forall_fibre_pow_torsionFree_algEquivZeroGroupCut
-- name    : ModularCurve.DRModelPackage.forall_fibre_pow_torsionFree_algEquivZeroGroupCut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/a750354d-a37d-56b6-9b03-c48c5a3d02a8
-- title:
--   No p-power torsion in the Pic⁰-cut on characteristic p fibres
-- statement:
--   Let $p$ be a prime and let $\mathfrak{X}$ be a `DRModelPackage p`, that is, a bundle of data and properties for the two-chart integral model `DRModel p` over $\mathbb{Z}$ of the modular curve attached to level $p$ (built as [`AlgebraicCurve.TwoChartIntegralModel`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) from the full modular function field and the Igusa coordinate `IgusaScheme.jFull p`), together with its structure morphism `DRModel.toBase p` to $\operatorname{Spec}\mathbb{Z}$, the two sections $\varepsilon_\infty,\varepsilon_0$ of that morphism and the further properness, flatness, integrality, normality, generic-fibre and smooth-locus data; and let $I$ be a `LegTwoInput` for $\mathfrak{X}$, the auxiliary block of covering, fibre-cohomology, reducedness, genus and étale-pool data. The assertion is: for every type $K$ that is an algebraically closed field of characteristic $p$, every $k \in \mathbb{N}$, and every element $\xi$ of the value at the opposite of the object $\operatorname{Spec} K \to \operatorname{Spec}\mathbb{Z}$ of $(\operatorname{Spec}\mathbb{Z})$-schemes of the presheaf `relSubPicPresheaf` of $\varepsilon_\infty$-rigidified line-bundle classes on the base change of `DRModel.toBase p` that lie in the cut `algEquivZeroGroupCut`, namely the fibrewise algebraic-equivalence-to-zero condition, which is closed under tensor product and inverses and hence makes these classes into a commutative group via `commGroupObj`, the relation $\xi^{p^k} = 1$ forces $\xi = 1$.
--
--   This is the statement that the $\operatorname{Pic}^0$-cut class group on the geometric fibre in characteristic $p$ of the Deligne–Rapoport model is free of $p$-power torsion, reflecting the fact that this fibre is a nodal curve whose $\operatorname{Pic}^0$ is a torus over a field of characteristic $p$. It is the torsion-freeness hypothesis used by [`ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin`](thm.html#ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin) in the construction of the Néron identity component attached to the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_forall_fibre_pow_torsionFree_algEquivZeroGroupCut.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve
open scoped CategoryTheory.MonObj

theorem ModularCurve.DRModelPackage.forall_fibre_pow_torsionFree_algEquivZeroGroupCut
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (I : 𝔛.LegTwoInput) :
    ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (k : ℕ),
      letI := (algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf).commGroupObj
        (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))
      ∀ ξ : (relSubPicPresheaf (DRModel.toBase p) 𝔛.εinf (algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf).toSubPicCondition).obj
          (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))), ξ ^ (p ^ k) = 1 → ξ = 1 := by sorry
