-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_abelian_picard_abelJacobi_charZero
-- name    : MazurTransfer.order13_actual_abelian_picard_abelJacobi_charZero
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T10:02:01.854004+00:00
-- url     : https://prove2.me/theorems/34b37438-e705-4b6a-a825-ff97aac8ea01
-- title:
--   Abelian Picard scheme and full Abel–Jacobi dictionary for the actual order-13 curve
-- statement:
--   Let $k_0$ be any characteristic-zero field and let $C/k_0$ be the actual two-chart curve
--   $$y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1,$$
--   with reciprocal gluing $z=x^{-1}$ and $w=yx^{-3}$. The curve has a rational section. For every rational section $\varepsilon$, there exist a genuine relative Picard designation $P/k_0$, its full representing witness for the rigidified algebraically trivial line-bundle functor, a relative group law, and a morphism
--   $$a_\varepsilon:C\longrightarrow P.$$
--   The structure morphism of $P$ is smooth, proper and geometrically connected, and satisfies the original abelian-scheme property bundle. The relative group law is commutative, its identity is the designated zero section, and $a_\varepsilon(\varepsilon)=0$.
--
--   For every algebraically closed field fibre and every compatible function-field curve model of that fibre, its degree-zero divisor-class group is identified with the fibre's points on $P$, compatibly with addition. Under this identification, a point difference $[x-s]$, where $s$ lies over $\varepsilon$, maps to $a_\varepsilon(x)$.
--
--   All of these conclusions apply over the original base $k_0=\mathbb Q$. The divisor-class points dictionary retains its algebraically closed fibre hypothesis. No modular identification, injectivity, Jacobian rank, rational-point obstruction or full Mazur classification is asserted by this intermediate theorem.
-- source:
--   Actual curve: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/AlgebraicGeometry . Full relative group-law and Abel–Jacobi dictionary: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic.lean . Actual characteristic-zero curve model, geometric integrality and Picard representation proved by Vas and contributors on Prove2Me. Apache-2.0 attribution retained; the full original conclusion and its field-fibre quantifiers are preserved.

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

theorem MazurTransfer.order13_actual_abelian_picard_abelJacobi_charZero.{u, v} (k₀ : Type u) [Field k₀] [CharZero k₀] :
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
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : k₀ →+* K)
        (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase,
          (∀ x y : Pic0 K F,
            pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) (Spec.map (CommRingCat.ofHom i)) =
              Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ Dv : Divisor.degZero (K := K) (F := F),
              (Dv : Divisor K F) =
                Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk Dv)).1 =
                x.1 ≫ e ≫ pullback.fst (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase k₀) (Spec.map (CommRingCat.ofHom i)) ≫ aj.1 := by sorry
