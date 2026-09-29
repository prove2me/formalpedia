-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_symm_fibreMap_frobeniusNormHom_eq_frobeniusPushforwardModL_symm
-- name    : ModularCurve.JZeroNeronObjectAtP.LevelModel.symm_fibreMap_frobeniusNormHom_eq_frobeniusPushforwardModL_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/102ae18d-d19b-5443-91e6-c784857a2367
-- title:
--   Norm along φ_κ acts as Frobenius pushforward on Pic⁰
-- statement:
--   Fix $N_0\ge 1$ and a prime $p$ with $p\nmid N_0$, a Deligne–Rapoport model package $\mathfrak P$ at level $N_0p$, a valuation subring $A$ of $\overline{\mathbf Q}$ in which $p$ is a non-unit, whose residue field $\kappa$ has characteristic $p$, and a level model $M$ of the Jacobian of $X_0(N_0)$ at $A$ whose underlying level data `M.toLevelData` satisfies `IsJacobian` (an abelian-scheme property bundle, commutativity of the relative group law, additivity and Galois equivariance of the generic point dictionary, additivity of the special dictionary, agreement of reduction of points with reduction of divisor classes modulo the residue characteristic, and Hecke compatibility). Regard $\kappa$ as an $R_p$-algebra through `M.toκ`. The assertion is then universally quantified over: representability data `hD₀κ` exhibiting the base change $D_{0,\kappa}$ as representing the relative rigidified $\mathrm{Pic}^0$ of the $\kappa$-fibre of Igusa's model with the base-changed cusp section, cut out by the fibrewise algebraically-equivalent-to-zero condition; an isomorphism of its Poincaré bundle with the base change along $\kappa$ of the pullback of $M$'s Poincaré bundle along the first projection; an endomorphism $\varphi_\kappa$ of the $\kappa$-fibre `fibre0` equal to the composite of $\mathfrak P$'s component map `𝔓.comp` at index $1$ followed by `fibreMap0 𝔓.π`, lying over $\kappa$, finite, flat, locally of finite presentation, with $\varphi_\kappa$-fibre rank $p$ at every point; an endomorphism $F$ of $D_{0,\kappa}$ over $\kappa$ which classifies the norm along $\varphi_\kappa$, in the sense that for every $\kappa$-scheme $t:T\to\operatorname{Spec}\kappa$ and every $b$ over $t$ the pullback of the Poincaré bundle along $b$ followed by $F$ is isomorphic to the rigidification, along the cusp section and the projection, of the degree-$p$ norm module of the pullback along $b$ taken with respect to the curve change induced by $\varphi_\kappa$; and a bijection $e:\mathrm{Pic}^0(F_{N_0,\kappa})\to D_{0,\kappa}(\kappa)$ whose underlying morphisms agree with those of `M.ptsSp`. For every $\kappa$-point $b$ of $D_0$ over $\operatorname{Spec}\kappa$, the conclusion is $e^{-1}(\,b\ \text{acted on by}\ F\,)=\mathrm{frobeniusPushforwardModL}_{\kappa,N_0,p}(e^{-1}(b))$, the action of $F$ being composition of $b$, transported to a fibre point, with $F$.
--
--   This is the special-fibre dictionary for the Jacobian of $X_0(N_0)$: under the mod-$p$ point dictionary, the endomorphism classifying the norm along the degree-$p$ fibre map $\varphi_\kappa$ corresponds to the Frobenius pushforward on divisor classes of the modular function field over $\kappa$. It is used in [`ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel`](thm.html#ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel), where the special fibre of the level-$N_0p$ model is analysed together with the degeneracy maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_symm_fibreMap_frobeniusNormHom_eq_frobeniusPushforwardModL_symm.lean

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
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel IsLocalRing

theorem ModularCurve.JZeroNeronObjectAtP.LevelModel.symm_fibreMap_frobeniusNormHom_eq_frobeniusPushforwardModL_symm
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p]

    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) (hΛ : M.toLevelData.IsJacobian) :
    letI : Algebra (R p) (ResidueField ↥A) := M.toκ.toAlgebra
    letI := instDecidableEqResidueFieldSemistable A
    ∀
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀))
        (M.D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) M.ε₀ (ResidueField ↥A)
        (M.rep.poincare.pullbackAlong ⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))

      (φκ : fibre0 (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))
      (_ : φκ = 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1 ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A)))
      (hφκ_over : φκ ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))
      [IsFinite φκ] [Flat φκ] [LocallyOfFinitePresentation φκ] (_ : ∀ x, φκ.finrank x = p)

      (F : SchemeHomOver (M.D₀.baseChange (ResidueField ↥A)).toBase (M.D₀.baseChange (ResidueField ↥A)).toBase)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
          (b : SchemeHomOver t (M.D₀.baseChange (ResidueField ↥A)).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b F)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t
              (sectionBaseChange (ResidueField ↥A) M.ε₀))
              (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t)
            (Scheme.Modules.normModule (curveChange φκ hφκ_over t) p (hD₀κ.poincare.pullbackAlong b).L)))

      (e : JZeroC (ResidueField ↥A) N₀ ≃ SchemeHomOver (specMap (R p) (ResidueField ↥A)) M.D₀.toBase)
      (_ : ∀ u : JZeroC (ResidueField ↥A) N₀, (e u).1 = (M.ptsSp u).1)
      (b : SchemeHomOver (specMap (R p) (ResidueField ↥A)) M.D₀.toBase),
      e.symm (ModularCurve.JZeroNeronObjectAtP.fibreMap F b) = frobeniusPushforwardModL (ResidueField ↥A) N₀ p (e.symm b) := by sorry
