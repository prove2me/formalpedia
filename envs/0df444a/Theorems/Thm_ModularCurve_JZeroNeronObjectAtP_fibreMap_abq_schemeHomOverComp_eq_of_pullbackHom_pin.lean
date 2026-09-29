-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_fibreMap_abq_schemeHomOverComp_eq_of_pullbackHom_pin
-- name    : ModularCurve.JZeroNeronObjectAtP.fibreMap_abq_schemeHomOverComp_eq_of_pullbackHom_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/5ebfd64d-cb00-5f27-a47d-07fc5b489fe6
-- title:
--   Degeneracy maps on Pic⁰ commute with base twists
-- statement:
--   Fix a positive integer $N_0$ and a prime $p$ with $p \nmid N_0$, a package $\mathfrak{P}$ of Deligne–Rapoport model data at level $N_0p$ (the structure `DRModelPackageLevel`, which equips the Igusa-type scheme $X$ with its structure morphism `toBase N₀ p` over $R =$ `R p`, a cusp section $\mathfrak{P}.\varepsilon_{\mathrm{inf}}$, and, for each algebraically closed residue field, two component morphisms), and an algebraically closed field $\kappa$ of characteristic $p$ with an $R$-algebra structure. Let $D$ be a pointed $R$-scheme (a `RelativePic0Designation`: a scheme $P$ with a structure morphism to $\operatorname{Spec} R$ and a zero section) together with data $hD$ exhibiting $D$ as representing rigidified line bundles on `toBase N₀ p` rigidified along $\mathfrak{P}.\varepsilon_{\mathrm{inf}}$ and satisfying the fibrewise condition `algEquivZeroCut` (fibrewise algebraic equivalence to zero over algebraically closed fields), and let $\varepsilon_0$, $D_0$, $hD_0$ be the same data for `toBase0 N₀ p`. Assume further given representing data $hD_\kappa$, $hD_{0\kappa}$ for the base changes $D \times_R \kappa$ and $D_0 \times_R \kappa$, with $hPD$, $hPD_0$ asserting that their Poincaré bundles are isomorphic to the base changes along `BaseChange.ofR` of the Poincaré bundles of $hD$, $hD_0$; and assume $h\varepsilon_1'$: the base-changed section of $\varepsilon_0$ followed by the component morphism $\mathfrak{P}.\mathrm{comp}\ \kappa\ 0$ equals the base-changed section of $\mathfrak{P}.\varepsilon_{\mathrm{inf}}$. Let $\mathrm{abq} : \mathrm{Fin}\,2 \to$ morphisms $D_\kappa \to (D_0)_\kappa$ over $\operatorname{Spec}\kappa$ be given, with $\mathrm{abq}\,0$ equal to the map classifying pullback of the Poincaré bundle along the zeroth component morphism (`RepresentsRelSubPic.pullbackHom`), and with $\mathrm{abq}\,1$ characterised by $habq_1$: for every $\kappa$-scheme $t : T \to \operatorname{Spec}\kappa$ and every point $a$ of $D_\kappa$ over $t$, the pullback of the Poincaré bundle of $hD_{0\kappa}$ along $a$ followed by $\mathrm{abq}\,1$ is isomorphic to the rigidification along the canonical section of the pullback, under the curve-change morphism attached to the first component morphism, of the pullback of the Poincaré bundle of $hD_\kappa$ along $a$. The conclusion: for every endomorphism $\tau$ of $\operatorname{Spec}\kappa$ over $\operatorname{Spec} R$, every $i \in \mathrm{Fin}\,2$ and every $\kappa$-point $x$ of $D$ over $\operatorname{Spec} R$, the map on fibres induced by $\mathrm{abq}\,i$ applied to $\tau$ followed by $x$ equals $\tau$ followed by the value of that map on $x$; that is, the two degeneracy maps commute with twisting $\kappa$-points by $\tau$.
--
--   This is the twist-equivariance clause for the two degeneracy (abelian-quotient) maps from the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model of $X_0(N_0p)$ to that of $X_0(N_0)$, over an algebraically closed residue field of characteristic $p$; it expresses that these maps are defined over the prime field, hence compatible with Frobenius and with the action of a decomposition group. It is used in the assembly of the special-fibre data of the Néron object of $J_0(N_0p)$ at $p$, as cited by [`ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel`](thm.html#ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_fibreMap_abq_schemeHomOverComp_eq_of_pullbackHom_pin.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.JZeroNeronObjectAtP.fibreMap_abq_schemeHomOverComp_eq_of_pullbackHom_pin
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
    (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀)

    (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)
      (algEquivZeroCut (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)) (D.baseChange κ))
    (hPD : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf κ
      (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) κ), pullback.condition⟩)).L))
    (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)
      (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)) (D₀.baseChange κ))
    (hPD₀ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) ε₀ κ
      (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) κ), pullback.condition⟩)).L))
    (hε₁' : (sectionBaseChange κ ε₀).1 ≫ 𝔓.comp κ (algebraMap (R p) κ) 0 = (sectionBaseChange κ 𝔓.εinf).1)

    (abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (D₀.baseChange κ).toBase)
    (habq₀ : abq 0 = RepresentsRelSubPic.pullbackHom (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp_over κ (algebraMap (R p) κ) 0)
      hε₁' hDκ hD₀κ)
    (habq₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
      Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
            (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
          ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) 1)
            (𝔓.comp_over κ (algebraMap (R p) κ) 1) t)).obj (hDκ.poincare.pullbackAlong a).L))) :
    ∀ (τ : SchemeHomOver (specMap (R p) κ) (specMap (R p) κ)) (i : Fin 2) (x : SchemeHomOver (specMap (R p) κ) D.toBase),
      ModularCurve.JZeroNeronObjectAtP.fibreMap (abq i) (GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 x) =
        GoodReductionJacobian.schemeHomOverComp τ.1 τ.2 (ModularCurve.JZeroNeronObjectAtP.fibreMap (abq i) x) := by sorry
