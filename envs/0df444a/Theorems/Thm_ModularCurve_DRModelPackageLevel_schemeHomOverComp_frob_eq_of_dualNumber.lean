-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_schemeHomOverComp_frob_eq_of_dualNumber
-- name    : ModularCurve.DRModelPackageLevel.schemeHomOverComp_frob_eq_of_dualNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/11d2a86b-882b-5b10-b8ef-a035077b2393
-- title:
--   Norm endomorphism of Pic⁰ annihilates tangent vectors
-- statement:
--   Fix a prime $p$ and $N_0\ge 1$ with $p\nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel N₀ p hpN₀`, a model package for the Igusa-type scheme over $R_p$ with its two structure morphisms `toBase` and `toBase0`. Let $\varepsilon_0$ be a section of `toBase0 N₀ p` over $\mathrm{Spec}\,R_p$, let $D_0$ be a relative $\mathrm{Pic}^0$ designation for `toBase0 N₀ p` (a scheme $P$ with a structure morphism to $\mathrm{Spec}\,R_p$ and a zero section), and let $hD_0$ assert that $D_0$ represents the functor of rigidified line bundles on `toBase0` satisfying the fibrewise algebraic-equivalence-zero condition `algEquivZeroCut`. Let $\kappa$ be an algebraically closed field of characteristic $p$ with an $R_p$-algebra structure, and assume the base-changed designation $D_0^\kappa$ likewise represents the corresponding rigidified condition for the base-changed curve `baseChange (R p) (toBase0 N₀ p) κ` with section `sectionBaseChange κ ε₀`. Let $\varphi_\kappa$ be the endomorphism of the fibre `fibre0` given by `𝔓.comp κ (algebraMap (R p) κ) 1` followed by `fibreMap0 𝔓.π`, assumed to commute with the structure morphism to $\mathrm{Spec}\,\kappa$, finite, flat and locally of finite presentation, with `finrank` equal to $p$ at every point. Let $F$ be an endomorphism of $D_0^\kappa$.toBase over $\mathrm{Spec}\,\kappa$ which classifies the norm along $\varphi_\kappa$: for every $t:T\to\mathrm{Spec}\,\kappa$ and every $T$-point $b$ of $D_0^\kappa$.toBase, the pullback of the Poincaré bundle along $b$ followed by $F$ is isomorphic to the `rigidify`ication, along `rigSection` and `pullback.snd`, of `normModule (curveChange φκ hφκ_over t) p` applied to the pullback of the Poincaré bundle along $b$. Finally let $v$ be a $\kappa[\epsilon]$-point of $D_0^\kappa$.toBase over $\mathrm{Spec}\,\kappa[\epsilon]\to\mathrm{Spec}\,\kappa$ and $x$ a $\kappa$-point with $x$ obtained from $v$ by composing with $\mathrm{Spec}$ of the projection $\kappa[\epsilon]\to\kappa$. Then $v$ followed by $F$ equals the constant $\kappa[\epsilon]$-point $\mathrm{Spec}\,\kappa[\epsilon]\to\mathrm{Spec}\,\kappa\xrightarrow{x}D_0^\kappa$.toBase followed by $F$.
--
--   This is the vanishing of the differential of the Frobenius endomorphism of the Jacobian of $X_0(N_0)$ in characteristic $p$, realised as the morphism classifying the norm of rigidified line bundles along the degree-$p$ self-map $\varphi_\kappa$ of the special fibre: $F$ carries every tangent vector, i.e. every $\kappa[\epsilon]$-point, to the corresponding constant one. It feeds into the proof that the kernel of the induced norm homomorphism on the special fibre is reduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_schemeHomOverComp_frob_eq_of_dualNumber.lean

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

theorem ModularCurve.DRModelPackageLevel.schemeHomOverComp_frob_eq_of_dualNumber
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
    (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀)

    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)
      (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)) (D₀.baseChange κ))

    (φκ : fibre0 (N₀ := N₀) (algebraMap (R p) κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    (hφκ : φκ = 𝔓.comp κ (algebraMap (R p) κ) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) κ))
    (hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) κ = baseChange (R p) (toBase0 N₀ p) κ)
    [IsFinite φκ] [Flat φκ] [LocallyOfFinitePresentation φκ] (hφ_rk : ∀ x, φκ.finrank x = p)

    (F : SchemeHomOver (D₀.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (hF : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (b : SchemeHomOver t (D₀.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b F)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L)))

    (v : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) (D₀.baseChange κ).toBase)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (D₀.baseChange κ).toBase)
    (hx : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ v.1 = x.1) :
    NeronModelInfra.schemeHomOverComp v F =
      NeronModelInfra.schemeHomOverComp
        (⟨Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫ x.1,
          by rw [Category.assoc, x.2, Category.comp_id]⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) (D₀.baseChange κ).toBase) F := by sorry
