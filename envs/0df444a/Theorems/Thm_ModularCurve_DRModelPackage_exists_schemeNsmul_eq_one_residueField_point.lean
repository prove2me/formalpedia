-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_schemeNsmul_eq_one_residueField_point
-- name    : ModularCurve.DRModelPackage.exists_schemeNsmul_eq_one_residueField_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7a8192bc-4747-5d69-8a10-5dd42ad4d38c
-- title:
--   Residue-field points above p killed by [m], p∤ m
-- statement:
--   Let $p$ be a prime, let $\mathfrak X$ be a `DRModelPackage p`, that is a package of data (properness, flatness, integrality and normality of the two-chart integral model `DRModel p` over $\mathbb Z$ attached to the full modular function field and the Igusa $j$-invariant, generic and geometric curve models with their Galois compatibilities, two marked sections $\varepsilon_\infty,\varepsilon_0$, a smooth locus, and further data), and let $I$ be a `LegTwoInput` for $\mathfrak X$. Let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}\colon D.P\to\operatorname{Spec}\mathbb Z$ and a section of it, and let $hD$ assert that $D$ represents the subfunctor of $\varepsilon_\infty$-rigidified line bundles on `DRModel p` over $\operatorname{Spec}\mathbb Z$ cut out by the condition `FibrewiseAlgEquivZero`: a Poincaré rigidified bundle on the pullback along $D.\mathrm{toBase}$ satisfying that condition, the universal property that every rigidified bundle satisfying it over a base $t$ is, up to isomorphism of underlying line bundles, pulled back along a unique morphism over $t$, and triviality of the pullback along the zero section. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, and write $k_A$ for its residue field. Then for every morphism $\zeta\colon\operatorname{Spec}k_A\to D.P$ whose composite with $D.\mathrm{toBase}$ is the morphism induced by $\mathbb Z\to A\to k_A$, there is an $m>0$ with $p\nmid m$ such that $\zeta$ followed by the multiplication-by-$m$ endomorphism `schemeNsmul m` of the relative group law on $D.P$ coming from $hD$ equals $\zeta$ followed by $D.\mathrm{toBase}$ followed by the unit section of that group law at the identity of $\operatorname{Spec}\mathbb Z$.
--
--   This is the torsion input for the construction of Hecke endomorphisms on the relative $\operatorname{Pic}^0$ of the Deligne–Rapoport model: every residue-field point in characteristic $p$ of the representing scheme is annihilated by some multiplication-by-$m$ with $m$ prime to $p$. It is used in [`ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin`](thm.html#ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_schemeNsmul_eq_one_residueField_point.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve

theorem ModularCurve.DRModelPackage.exists_schemeNsmul_eq_one_residueField_point
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (I : 𝔛.LegTwoInput)
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∀ ζ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ D.P,
      ζ ≫ D.toBase = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A))) →
      ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧
        ζ ≫ (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).schemeNsmul m =
          ζ ≫ D.toBase ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).one (𝟙 _)).1 := by sorry
