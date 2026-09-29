-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_frobHom_classifies_normModule_baseChange
-- name    : ModularCurve.DRModelPackageLevel.exists_frobHom_classifies_normModule_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/1680aae9-a296-5e70-ad6e-266668245b9b
-- title:
--   Existence of the norm endomorphism on the special-fibre Pic⁰
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$, write $R=R(p)$ for the base ring and $c_0=$ `toBase0 N₀ p` for Igusa's model $X_0(N_0)$ over $\operatorname{Spec} R$. Let $\varepsilon_0$ be a section of $c_0$ (a morphism $\operatorname{Spec} R \to X_0(N_0)$ splitting $c_0$) and let $D_0$ be a `RelativePic0Designation` for $c_0$, i.e. a scheme $P$ with a structure morphism to $\operatorname{Spec} R$ together with a zero section splitting it. Let $\kappa$ be an algebraically closed field of characteristic $p$ that is an $R$-algebra, and let $c_\kappa$ be the base change of $c_0$ to $\kappa$, with induced section $\varepsilon_{0,\kappa}$. Assume `hD₀κ`: the base change $(D_0)_\kappa$ represents, with Poincaré bundle, the functor of $\varepsilon_{0,\kappa}$-rigidified invertible modules on $c_\kappa$ cut out by the condition that the bundle be algebraically equivalent to zero on every geometric fibre. Let $\varphi_\kappa$ be an endomorphism of the $\kappa$-fibre curve `fibre0` with $\varphi_\kappa$ followed by $c_\kappa$ equal to $c_\kappa$, which is finite, flat and locally of finite presentation with $\operatorname{finrank}$ equal to $p$ at every point. Then there exists an endomorphism $F$ of $(D_0)_\kappa$ over $\operatorname{Spec}\kappa$ (a morphism whose composite with the structure morphism of $(D_0)_\kappa$ is that structure morphism again) such that: (1) for every scheme $T$, every $t\colon T\to \operatorname{Spec}\kappa$ and every $T$-point $b$ of $(D_0)_\kappa$ over $t$, the pullback of the Poincaré bundle along $b$ followed by $F$ is isomorphic to the rigidification along $\operatorname{rigSection}(c_\kappa,t,\varepsilon_{0,\kappa})$, with respect to the projection $\operatorname{pullback.snd}(c_\kappa,t)$, of the norm module in degree $p$, namely $\det_p(\pi_*L)\otimes \det_p(\pi_*\mathcal{O})^{\vee}$ for $\pi$ the base change of $\varphi_\kappa$ to $T$ and $L$ the bundle classified by $b$; (2) $F$ is a homomorphism for the relative group law on $T$-points obtained from `hD₀κ` via the group-theoretic algebraic-equivalence cut, that is, composing a product of two $T$-points with $F$ gives the product of their composites with $F$; (3) the zero section of $(D_0)_\kappa$ followed by $F$ is the zero section.
--
--   This is the existence of the norm (Picard-functoriality) endomorphism of the special fibre of $\mathrm{Pic}^0$ of the level-$N_0$ modular curve attached to a finite flat self-map of degree $p$ of that fibre, pinned down by its effect on classified rigidified line bundles, together with its additivity and the preservation of the zero section. It supplies the pair consisting of the endomorphism and its classifying property under which the Ribet-style matrix identity on $\kappa$-points and the reducedness of the joint kernel of the two degeneracy morphisms are formulated, and it is used in the comparison of the Frobenius norm map with pushforward modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_frobHom_classifies_normModule_baseChange.lean

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

theorem ModularCurve.DRModelPackageLevel.exists_frobHom_classifies_normModule_baseChange
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime]
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)
      (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)) (D₀.baseChange κ))

    (φκ : fibre0 (N₀ := N₀) (algebraMap (R p) κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    (hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) κ = baseChange (R p) (toBase0 N₀ p) κ)
    [IsFinite φκ] [Flat φκ] [LocallyOfFinitePresentation φκ] (hφ_rk : ∀ x, φκ.finrank x = p) :
    ∃ F : SchemeHomOver (D₀.baseChange κ).toBase (D₀.baseChange κ).toBase,

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : SchemeHomOver t (D₀.baseChange κ).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b F)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
              (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
            (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L))) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (x y : SchemeHomOver t (D₀.baseChange κ).toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀κ).mul t x y) F =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀κ).mul t
            (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)) ∧

      (D₀.baseChange κ).zeroSection ≫ F.1 = (D₀.baseChange κ).zeroSection := by sorry
