-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_injective_monoidHom_algEquivZeroGroupCut_pFibre
-- name    : ModularCurve.DRModelPackage.exists_injective_monoidHom_algEquivZeroGroupCut_pFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/3b42fe11-e112-5cd1-93b1-32819367d6c5
-- title:
--   Node-ratio embedding of the Pic⁰ cut at p
-- statement:
--   Let $p$ be a prime, let $\mathfrak{X}$ be a `DRModelPackage p`, that is, a bundle of data and properties for the two-chart integral model `DRModel p` over $\mathbb{Z}$ built from the full modular function field with the Igusa coordinate `IgusaScheme.jFull p` (properness, flatness and integrality of the structure map `DRModel.toBase p`, normality on affine opens, rational and geometric curve models with their compatibilities, two sections $\varepsilon_\infty$, $\varepsilon_0$ of `DRModel.toBase p` over $\mathrm{Spec}\,\mathbb{Z}$, a smooth locus, and further data), let $I$ be a `LegTwoInput` for $\mathfrak{X}$ (a two-chart affine open cover, bijectivity of the base ring onto global sections after base change, affine refinements containing prescribed finite sets of points of the smooth locus, triviality of fibrewise algebraically trivial invertible modules possessing a nonzero section, reducedness of geometric fibres, a genus constant computing the first cohomology rank, and a pool of finite étale data over localisations; summarised here), and let $K$ be an algebraically closed field of characteristic $p$. Consider the sections over the object $\mathrm{Spec}\,K \to \mathrm{Spec}\,\mathbb{Z}$ of $\mathrm{Over}(\mathrm{Spec}\,\mathbb{Z})$ of the presheaf `relSubPicPresheaf` attached to `DRModel.toBase p`, the section $\varepsilon_\infty$ and the subcondition underlying `algEquivZeroGroupCut`, namely classes of $\varepsilon_\infty$-rigidified line bundles on the base change satisfying the fibrewise algebraic-equivalence-to-zero cut; these form an abelian group under tensor product via `SubPicGroupCondition.commGroupObj`. The assertion is that there exist $s \in \mathbb{N}$ and an injective monoid homomorphism from this group to $(\mathrm{Fin}\,s \to K^\times)$ modulo the image of the constant (diagonal) homomorphism $K^\times \to (\mathrm{Fin}\,s \to K^\times)$.
--
--   This records, in the form needed later, the classical description of the $\mathrm{Pic}^0$ part of the geometric characteristic-$p$ fibre of the Deligne–Rapoport model: the fibre is a union of two rational curves meeting at finitely many ordinary double points, and a rigidified line bundle trivial on each component is determined by its ratios at the $s$ nodes, up to a common scalar. It is the common input to the two torsion statements on this fibre, [`ModularCurve.DRModelPackage.forall_fibre_exists_pow_eq_one_algEquivZeroGroupCut`](thm.html#ModularCurve.DRModelPackage.forall_fibre_exists_pow_eq_one_algEquivZeroGroupCut) and [`ModularCurve.DRModelPackage.forall_fibre_pow_torsionFree_algEquivZeroGroupCut`](thm.html#ModularCurve.DRModelPackage.forall_fibre_pow_torsionFree_algEquivZeroGroupCut).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_injective_monoidHom_algEquivZeroGroupCut_pFibre.lean

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

theorem ModularCurve.DRModelPackage.exists_injective_monoidHom_algEquivZeroGroupCut_pFibre
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (I : 𝔛.LegTwoInput)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] :
    letI := (algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf).commGroupObj
      (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))
    ∃ (s : ℕ) (δ : (relSubPicPresheaf (DRModel.toBase p) 𝔛.εinf
          (algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf).toSubPicCondition).obj
          (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))) →*
        (Fin s → Kˣ) ⧸ (Pi.constMonoidHom (Fin s) Kˣ).range),
      Function.Injective δ := by sorry
