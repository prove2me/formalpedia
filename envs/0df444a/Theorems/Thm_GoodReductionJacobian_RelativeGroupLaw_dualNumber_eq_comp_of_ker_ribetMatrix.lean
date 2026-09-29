-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_dualNumber_eq_comp_of_ker_ribetMatrix
-- name    : GoodReductionJacobian.RelativeGroupLaw.dualNumber_eq_comp_of_ker_ribetMatrix
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/e50cc60b-14f4-5f5a-8123-b171c8ca39dd
-- title:
--   Dual-number points of the kernel of Ribet's matrix are constant
-- statement:
--   Let $\kappa$ be a field and let $sB : B \to \operatorname{Spec}\kappa$ be a scheme over $\kappa$, equipped with a `RelativeGroupLaw` $L$: for each test morphism $t : T \to \operatorname{Spec}\kappa$ a multiplication, unit and inversion on the set of $\varphi : T \to B$ with $\varphi \circ sB = t$ (written `SchemeHomOver t sB`), satisfying associativity, both unit laws and left inversion, and compatible with composition $\psi$ of test morphisms. Let $F$ be an endomorphism of $B$ with $sB \circ F = sB$, assumed to kill tangent vectors in the following sense: whenever $v : \operatorname{Spec}\kappa[\varepsilon] \to B$ lies over the structure morphism induced by $\kappa \to \kappa[\varepsilon]$ and $x : \operatorname{Spec}\kappa \to B$ is a section of $sB$ with $x$ equal to the composite of $\operatorname{Spec}$ of the projection $\kappa[\varepsilon] \to \kappa$ with $v$, then $F \circ v$ equals $F \circ x$ composed with $\operatorname{Spec}\kappa[\varepsilon] \to \operatorname{Spec}\kappa$. Over $P = B \times_{\operatorname{Spec}\kappa} B$, with $x_{BB}, y_{BB}$ the two projections viewed as points of $B$ over $t_{BB} = sB \circ \mathrm{pr}_1$, put $m_0 = x_{BB} \cdot (F \circ y_{BB})$, $m_1 = (F \circ x_{BB}) \cdot y_{BB}$, let $M : P \to P$ be the morphism with components $m_0, m_1$, and let $e_{BB} : \operatorname{Spec}\kappa \to P$ have both components the unit $L.\mathrm{one}$. The assertion is that every $w : \operatorname{Spec}\kappa[\varepsilon] \to \operatorname{Spec}\kappa \times_{P} \ldots$, that is every $\kappa[\varepsilon]$-point $w$ of the pullback of $M$ along $e_{BB}$ whose second projection is the canonical morphism $\operatorname{Spec}\kappa[\varepsilon] \to \operatorname{Spec}\kappa$, is constant: $w$ equals the composite of $\operatorname{Spec}\kappa[\varepsilon] \to \operatorname{Spec}\kappa$ with $\operatorname{Spec}$ of the projection $\kappa[\varepsilon]\to\kappa$ followed by $w$.
--
--   This is the functor-of-points form of the tangent-space computation for the kernel of Ribet's matrix $\begin{pmatrix} 1 & F \\ F & 1\end{pmatrix}$ on $B \times B$: when $F$ has vanishing differential, that kernel has no non-constant dual-number points, which is the input to the dual-number criterion for unramifiedness. It is used in the Deligne–Rapoport model setting to prove reducedness of the corresponding kernel scheme in [`ModularCurve.DRModelPackageLevel.isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq`](thm.html#ModularCurve.DRModelPackageLevel.isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_dualNumber_eq_comp_of_ker_ribetMatrix.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.dualNumber_eq_comp_of_ker_ribetMatrix
    {κ : Type u} [Field κ] {B : Scheme.{u}} (sB : B ⟶ Spec (CommRingCat.of κ)) (L : RelativeGroupLaw κ sB)
    (F : SchemeHomOver sB sB)
    (hF : ∀ (v : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) sB)
        (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) sB)
        (_ : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ v.1 = x.1),
      NeronModelInfra.schemeHomOverComp v F =
        NeronModelInfra.schemeHomOverComp
          (⟨Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫ x.1,
            by rw [Category.assoc, x.2, Category.comp_id]⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) sB) F) :

    let tBB : pullback sB sB ⟶ Spec (CommRingCat.of κ) := pullback.fst sB sB ≫ sB
    let xBB : SchemeHomOver tBB sB := ⟨pullback.fst sB sB, rfl⟩
    let yBB : SchemeHomOver tBB sB := ⟨pullback.snd sB sB, pullback.condition.symm⟩
    let m₀ := L.mul tBB xBB (NeronModelInfra.schemeHomOverComp yBB F)
    let m₁ := L.mul tBB (NeronModelInfra.schemeHomOverComp xBB F) yBB
    let Mx : pullback sB sB ⟶ pullback sB sB := pullback.lift m₀.1 m₁.1 (m₀.2.trans m₁.2.symm)
    let eBB : Spec (CommRingCat.of κ) ⟶ pullback sB sB := pullback.lift (L.one (𝟙 _)).1 (L.one (𝟙 _)).1 rfl
    ∀ w : Spec (CommRingCat.of (DualNumber κ)) ⟶ pullback Mx eBB,
      w ≫ pullback.snd Mx eBB = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) →
      w = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ w := by sorry
