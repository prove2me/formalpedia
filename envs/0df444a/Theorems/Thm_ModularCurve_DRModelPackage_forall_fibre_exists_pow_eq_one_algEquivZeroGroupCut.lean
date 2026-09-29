-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_forall_fibre_exists_pow_eq_one_algEquivZeroGroupCut
-- name    : ModularCurve.DRModelPackage.forall_fibre_exists_pow_eq_one_algEquivZeroGroupCut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/2aeb725a-1dad-5981-bddb-d1983e008627
-- title:
--   Prime-to-p torsion of cut classes on the geometric p-fibre
-- statement:
--   Let $p$ be a prime and let $\mathfrak X$ be a `DRModelPackage p`, i.e. a bundle of data and properties for the two-chart integral model `DRModel p` of the full modular curve of level $p$ over $\mathbb Z$ (properness, flatness and integrality of `DRModel.toBase p`, normality on affine opens, rational and geometric generic fibre curve models with their Galois and place compatibilities, two sections $\varepsilon_\infty,\varepsilon_0$ over $\mathbb Z$, a smooth locus, and further data summarised in the structure), and let $I$ be a `LegTwoInput` for $\mathfrak X$, a second block of data and hypotheses (a two-affine open cover, bijectivity of $A \to \Gamma$ on base changes, an affine-covering condition on finite sets in the smooth locus, triviality of rigidified invertible modules with a nonzero section on geometric fibres, reducedness of geometric fibres, a genus together with its $H^1$-rank identity, and an étale-pooling hypothesis, summarised here). The assertion is: for every type $K$ that is an algebraically closed field of characteristic $p$ in which every unit of $K$ has finite order, and for every element $\xi$ of the value at $\operatorname{op}(\operatorname{Spec} K \to \operatorname{Spec}\mathbb Z)$ of the presheaf `relSubPicPresheaf` of the sub-Picard cut `algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf` (fibrewise algebraic equivalence to zero, a condition closed under tensor product and inverses, so that this value carries the commutative group structure `commGroupObj`), there exists $m \in \mathbb N$ with $m > 0$, $p \nmid m$ and $\xi^m = 1$.
--
--   This is the fibre-by-fibre torsion input needed to control the $\operatorname{Pic}^0$-type cut of rigidified line bundles on the characteristic-$p$ geometric fibre of the Deligne–Rapoport model, where that fibre is not smooth. It feeds [`ModularCurve.DRModelPackage.exists_schemeNsmul_eq_one_residueField_point`](thm.html#ModularCurve.DRModelPackage.exists_schemeNsmul_eq_one_residueField_point), on the way to the prime-to-$p$ statements used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_forall_fibre_exists_pow_eq_one_algEquivZeroGroupCut.lean

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

theorem ModularCurve.DRModelPackage.forall_fibre_exists_pow_eq_one_algEquivZeroGroupCut
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (I : 𝔛.LegTwoInput) :
    ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K], (∀ u : Kˣ, IsOfFinOrder u) →
      letI := (algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf).commGroupObj
        (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))
      ∀ ξ : (relSubPicPresheaf (DRModel.toBase p) 𝔛.εinf (algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf).toSubPicCondition).obj
          (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))),
        ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧ ξ ^ m = 1 := by sorry
