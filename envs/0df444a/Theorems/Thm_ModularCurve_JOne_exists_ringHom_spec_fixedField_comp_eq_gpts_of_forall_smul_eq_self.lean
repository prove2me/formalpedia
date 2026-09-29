-- Prove2me | Theorems.Thm_ModularCurve_JOne_exists_ringHom_spec_fixedField_comp_eq_gpts_of_forall_smul_eq_self
-- name    : ModularCurve.JOne.exists_ringHom_spec_fixedField_comp_eq_gpts_of_forall_smul_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/7a09bb49-78e3-5917-9410-e0c3eefc4b23
-- title:
--   Descent of an H-invariant point of J₁(Mp) to the fixed field
-- statement:
--   Fix a prime $p$ and a nonzero $M$, a commutative ring $A$, a field $L$ that is an $A$-algebra, and $A$- and $L$-algebra structures on $\overline{\mathbb{Q}}$ forming a scalar tower. Let $f \colon X \to \operatorname{Spec} A$ be a scheme over $A$ with a section $\varepsilon$, and let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} A$ and a zero section, assumed (via `hrep`) to carry a Poincaré bundle representing, with its universal property, the functor of $\varepsilon$-rigidified invertible modules on $X/A$ that are fibrewise algebraically equivalent to zero; `hgadd` says that the given bijection `gpts` from $J_1(Mp) = \mathrm{Pic}^0$ of the field $\overline{\mathbb{Q}}\cdot\mathbb{Q}(X_1(Mp))$ of $q$-expansions onto the set of morphisms $\operatorname{Spec}\overline{\mathbb{Q}} \to D.P$ over $\operatorname{Spec} A$ is additive for the relative group law induced by that representability. Further data: a curve model $M_\eta$ over $\overline{\mathbb{Q}}$ of that function field (integral, proper, smooth of relative dimension $1$, with its bijection between closed points and places), an isomorphism $e_\eta \colon M_\eta.C \to X \times_{\operatorname{Spec} A} \operatorname{Spec}\overline{\mathbb{Q}}$ over $\overline{\mathbb{Q}}$; the equivariance `hgal`, saying that for $g \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing the image of $L$ pointwise and $\overline{\mathbb{Q}}$-points $x, x'$ of $M_\eta.C$ with $x'$ mapping into $X$ as $\operatorname{Spec}(g)$ followed by $x$, the place of $x'$ is the `arithmeticGalois` translate by $g$ of the place of $x$; a section `ajL` of $(D.\mathrm{baseChange}\ L).\mathrm{toBase}$ over $X \times_A L$, the canonical comparison $k_L$ between the base changes of $f$ to $\overline{\mathbb{Q}}$ and to $L$, the induced $\bar a_j \colon M_\eta.C \to D.P$, a $\overline{\mathbb{Q}}$-point $\bar\varepsilon$ of $M_\eta.C$ lying over $\varepsilon$, and `hpts_aj`, which for all $\overline{\mathbb{Q}}$-points $x, s$ of $M_\eta.C$ with $s$ over $\varepsilon$ produces a degree-zero divisor equal to $(\text{place of } x) - (\text{place of } s)$ whose image under `gpts` is $x$ followed by $\bar a_j$. Finally let $H \le \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be a subgroup fixing the image of $L$ pointwise and let $x \in J_1(Mp)$ satisfy $\sigma \cdot x = x$ for all $\sigma \in H$. Then there are a ring homomorphism $\rho_T$ from $A$ to the fixed field of $H$, regarded as a subfield of $\overline{\mathbb{Q}}$, and a morphism $y_T \colon \operatorname{Spec}(\overline{\mathbb{Q}}^H) \to D.P$ such that $\rho_T$ followed by the inclusion of $\overline{\mathbb{Q}}^H$ is the structure map $A \to \overline{\mathbb{Q}}$, the spectrum of that inclusion followed by $y_T$ is the point `gpts x`, and $y_T$ followed by $D.\mathrm{toBase}$ is $\operatorname{Spec}(\rho_T)$.
--
--   This is the Galois-descent step for points of the Picard scheme of $X_1(Mp)$: a divisor class fixed by a subgroup $H$ of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acting trivially on $L$ is realised by a point of the Picard scheme defined over the fixed field $\overline{\mathbb{Q}}^H$, together with a compatible $\overline{\mathbb{Q}}^H$-algebra structure on the base ring $A$. It feeds the construction of points with prescribed reduction behaviour on $X_1(Mp)$ used further on in the level-lowering analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_exists_ringHom_spec_fixedField_comp_eq_gpts_of_forall_smul_eq_self.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.JOne.exists_ringHom_spec_fixedField_comp_eq_gpts_of_forall_smul_eq_self
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (A : Type) [CommRing A]
    (L : Type) [Field L] [Algebra A L]
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of A))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) f)
    (D : RelativePic0Designation A f)
    (hrep : Nonempty (RepresentsRelSubPic f ε (algEquivZeroCut f ε) D))
    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback f (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd f (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)
    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst f (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst f (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)
    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (ajL : SchemeHomOver (baseChange A f L) (D.baseChange L).toBase)
    (kL : pullback f (specMap A (AlgebraicClosure ℚ)) ⟶ pullback f (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hkL₁ : kL ≫ pullback.fst f (specMap A L) = pullback.fst f (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd f (specMap A L) = pullback.snd f (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst f (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst f (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    (H : Subgroup ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)))
    (hH : ∀ σ ∈ H, ∀ l : L, σ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l)
    (x : ModularCurve.JOne (M * p)) (hxH : ∀ σ ∈ H, σ • x = x) :
    ∃ (ρT : A →+* ↥(IntermediateField.fixedField H).toSubfield)
      (yT : Spec (CommRingCat.of ↥(IntermediateField.fixedField H).toSubfield) ⟶ D.P),
      (IntermediateField.fixedField H).toSubfield.subtype.comp ρT = algebraMap A (AlgebraicClosure ℚ) ∧
      Spec.map (CommRingCat.ofHom (IntermediateField.fixedField H).toSubfield.subtype) ≫ yT = (gpts x).1 ∧
      yT ≫ D.toBase = Spec.map (CommRingCat.ofHom ρT) := by sorry
