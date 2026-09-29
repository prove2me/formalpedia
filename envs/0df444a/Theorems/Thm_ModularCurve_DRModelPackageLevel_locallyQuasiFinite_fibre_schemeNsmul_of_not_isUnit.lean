-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_locallyQuasiFinite_fibre_schemeNsmul_of_not_isUnit
-- name    : ModularCurve.DRModelPackageLevel.locallyQuasiFinite_fibre_schemeNsmul_of_not_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/23ede687-1043-50d4-abd4-f9ba4e2d0136
-- title:
--   Locally quasi-finite [n] on a fibre where n is non-invertible
-- statement:
--   Fix $N_0 \ge 1$ and a prime $p$ with $p \nmid N_0$, and let $R(p)$ be the associated base ring, with $X(N_0,p) \to \operatorname{Spec} R(p)$ the structure morphism `toBase N₀ p` of Igusa's scheme at level $N_0p$. Let $\mathfrak P$ be a Deligne–Rapoport model package at this level (properness, flatness, integrality and local finite presentation of the structure morphism, integral closedness on affine opens, a curve model over $\overline{\mathbf Q}$ matched with the geometric generic fibre together with its Galois compatibility and cusp normalisations, smoothness and geometric integrality of the rational fibre, and distinguished sections $\varepsilon_\infty$, $\varepsilon_0$, among further data), and write $\varepsilon_\infty = \mathfrak P.\mathtt{\varepsilon inf}$ for its cusp section. Let $D$ consist of a scheme with a morphism `D.toBase` to $\operatorname{Spec} R(p)$ and a section of it, and let $hD$ witness that $D$ represents the subfunctor of the relative Picard functor of $(X(N_0,p),\varepsilon_\infty)$ cut out by the condition that a rigidified line bundle be fibrewise algebraically equivalent to zero: a Poincaré rigidified line bundle over `D.toBase` satisfying that condition, the universal property that every rigidified line bundle over a base $t$ satisfying it is induced, up to isomorphism of line bundles, by a unique morphism over $\operatorname{Spec} R(p)$ to `D.toBase`, and the vanishing normalisation along the given section. Assume `D.toBase` smooth. Let $s$ be a point of $\operatorname{Spec} R(p)$, and let $n \ge 1$ be an integer whose image in the residue field of $\operatorname{Spec} R(p)$ at $s$ is not a unit. Then multiplication by $n$, formed from the relative group law on `D.toBase` supplied by $hD$ by passing to the fibre at $s$ over that residue field, is a locally quasi-finite morphism of the fibre to itself.
--
--   This is the special-fibre case of the assertion that $[n]$ on the $\operatorname{Pic}^0$ model of the Deligne–Rapoport model of $X_0(N_0p)$ is quasi-finite, in the regime where $n$ is not invertible on the fibre (so the fibre group law is not étale over its base). It is the input at the closed point for [`ModularCurve.DRModelPackageLevel.nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic`](thm.html#ModularCurve.DRModelPackageLevel.nsmul_flat_surjective_locallyQuasiFinite_of_representsRelSubPic), which combines it with the generic-fibre statement to get flatness, surjectivity and local quasi-finiteness of $[n]$ on the whole model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_locallyQuasiFinite_fibre_schemeNsmul_of_not_isUnit.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.locallyQuasiFinite_fibre_schemeNsmul_of_not_isUnit
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    [Smooth D.toBase]
    (s : Spec (CommRingCat.of (R p))) (n : ℕ) (hn : 0 < n) (hs : ¬ IsUnit ((n : GoodReductionJacobian.RelativeGroupLaw.baseResidueField s))) :
    LocallyQuasiFinite
      (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase N₀ p) 𝔓.εinf) hD).fibre s).schemeNsmul n) := by sorry
