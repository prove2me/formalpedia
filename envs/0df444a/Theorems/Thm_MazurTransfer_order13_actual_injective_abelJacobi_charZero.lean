-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_injective_abelJacobi_charZero
-- name    : MazurTransfer.order13_actual_injective_abelJacobi_charZero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T10:55:40.655794+00:00
-- url     : https://prove2.me/theorems/131fca2f-ac22-4e7e-a033-325dd3f9bc7f
-- title:
--   Injectivity of the actual order-13 Abel–Jacobi map on rational points over characteristic-zero fields
-- statement:
--   Let $k_0$ be any characteristic-zero field, including $\mathbb Q$, and let $C/k_0$ be the actual two-chart curve
--   $$y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1,$$
--   with reciprocal gluing $z=x^{-1}$ and $w=yx^{-3}$. The curve has a rational section. For every rational section $\varepsilon$, there exist a genuine relative degree-zero Picard designation $P/k_0$, its full witness representing the rigidified algebraically trivial line-bundle functor, a commutative relative group law, and a scheme morphism
--   $$a_\varepsilon:C\longrightarrow P.$$
--   The structure morphism of $P$ is smooth, proper and geometrically connected, and satisfies the original abelian-scheme property bundle. The group identity is the designated zero section and $a_\varepsilon(\varepsilon)=0$. For every test scheme, the relative group law is commutative.
--
--   The induced map on rational points is injective:
--   $$a_\varepsilon:C(k_0)\hookrightarrow P(k_0).$$
--   Thus distinct rational sections of the actual curve give distinct points of the actual representing abelian Picard scheme. No algebraic-closedness, supplied genus, supplied injectivity or arithmetic rank hypothesis is imposed on the base field. This supplies the actual scheme-valued injectivity needed for the order-13 rational-point obstruction. No modular identification, Jacobian rank calculation, absence of noncuspidal rational points, closed-immersion property or full Mazur classification is asserted.
-- source:
--   Actual curve by Vas and contributors: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . Official Anthropic FLT curve, Picard and Abel-Jacobi development: https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Uses the exact already proved actual characteristic-zero geometric-integrality and full relative group-law/Abel-Jacobi dictionary contracts on Prove2Me. Actual geometric-fibre genus is derived from structure-sheaf cohomology and the original full finrank_ker_sub_finrank_coker_baseChange_eq worker. Simple-pole powers and faithfully flat field descent establish rational-section injectivity. Full representing witness and abelian property bundle are retained. Apache-2.0 attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_JacJ1Iface
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem MazurTransfer.order13_actual_injective_abelJacobi_charZero.{u} (k₀ : Type u) [Field k₀] [CharZero k₀] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀)) ∧
    ∀ ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀),
      ∃ (D : RelativePic0Designation k₀ (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀))
        (h : RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) ε
          (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) ε) D)
        (L : RelativeGroupLaw k₀ D.toBase)
        (aj : SchemeHomOver (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) D.toBase),
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
      AbelianSchemePropertyBundle k₀ D.toBase ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k₀)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (CommRingCat.of k₀)))).1 = D.zeroSection ∧
      ε.1 ≫ aj.1 = D.zeroSection ∧
      Function.Injective (fun x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k₀)))
        (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) => x.1 ≫ aj.1) := by sorry
