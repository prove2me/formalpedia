-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_representsRelSubPic_torus_abq_specialFibre
-- name    : ModularCurve.DRModelPackageLevel.exists_representsRelSubPic_torus_abq_specialFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/21721262-1878-533e-94f9-9a4f14fdeb90
-- title:
--   Special fibre of Pic⁰ of the Deligne–Rapoport model
-- statement:
--   Fix $N_0 \ge 1$ and a prime $p$ with $p \nmid N_0$, a level package $\mathfrak P :$ `DRModelPackageLevel N₀ p hpN₀` for the model `X N₀ p` over $\operatorname{Spec}(R_p)$, and an algebraically closed field $\kappa$ of characteristic $p$ that is an $R_p$-algebra. Let $D$ be a relative $\mathrm{Pic}^0$ designation for `toBase N₀ p` (a scheme over $R_p$ together with a zero section splitting its structure map) and let $hD$ witness that $D$ represents, relative to the section $\mathfrak P.\varepsilon_{\inf}$, the subfunctor of rigidified line bundles that are fibrewise algebraically equivalent to zero; let $\varepsilon_0$ be a section of `toBase0 N₀ p`, and $D_0$, $hD_0$ the corresponding data for `toBase0 N₀ p` and $\varepsilon_0$. Assume the $\kappa$-fibre of `toBase N₀ p` is proper and the $\kappa$-fibre of `toBase0 N₀ p` is proper, smooth of relative dimension $1$ and geometrically integral. Assume further a $\kappa$-point $\varepsilon_{0\kappa}$ of the $\kappa$-fibre `fibre0` of `toBase0 N₀ p` whose two pullback components are $\operatorname{Spec}$ of $R_p \to \kappa$ followed by $\varepsilon_0$ and the identity, and which is carried by the component morphism $\mathfrak P.\mathrm{comp}\,\kappa\,0$ to the section `sectionFibre 𝔓.εinf`. Write $s$ for the number of elements of `ssPlaces p N₀ κ`, the set of supersingular places of the level-$N_0$ modular function field over $\kappa$. The conclusion asserts: the underlying set of the fibre product of the two component morphisms $\mathfrak P.\mathrm{comp}\,\kappa\,0$ and $\mathfrak P.\mathrm{comp}\,\kappa\,1$ has exactly $s$ elements; $s > 0$; and there exist representability data $hD_\kappa$ for `D.baseChange κ` over the $\kappa$-fibre of `toBase N₀ p` with section `sectionBaseChange κ 𝔓.εinf`, and $hD_{0\kappa}$ for `D₀.baseChange κ`, each pinned by an isomorphism of its Poincaré bundle with the base change along $\operatorname{Spec} \kappa$ of the pullback of the corresponding Poincaré bundle over $R_p$, together with the identity $hε₁'$ expressing that the base-changed $\varepsilon_0$ followed by $\mathfrak P.\mathrm{comp}\,\kappa\,0$ is the base-changed $\varepsilon_{\inf}$, a morphism $\tau$ over $\kappa$ from the split torus `torusStr κ (s-1)` (the spectrum of the group algebra $\kappa[\mathbb Z^{s-1}]$) to the total space of `D.baseChange κ`, and a pair $abq : \mathrm{Fin}\,2 \to$ morphisms over $\kappa$ from that total space to the total space of `D₀.baseChange κ`, such that: $abq\,0$ is the classifying morphism `RepresentsRelSubPic.pullbackHom` attached to $\mathfrak P.\mathrm{comp}\,\kappa\,0$; for every $\kappa$-scheme $t : T \to \operatorname{Spec}\kappa$ and every $T$-point $a$ of `D.baseChange κ`, the Poincaré bundle pulled back along $a$ followed by $abq\,1$ is isomorphic to the rigidification, at `rigSection` for the base-changed $\varepsilon_0$ and the projection, of the pullback along `curveChange` of $\mathfrak P.\mathrm{comp}\,\kappa\,1$ of the bundle classified by $a$; $\tau$ is a closed immersion; $\tau$ is multiplicative on the $\kappa$-points `torusPtId` indexed by $\chi, \chi'$ in `WithConv (torusCoord κ (s-1) →ₐ[κ] κ)`, in the sense that the point attached to $\chi\chi'$ is the product, for the base change along $\operatorname{Spec}\kappa$ of the relative group law of $hD$, of the points attached to $\chi$ and $\chi'$; each $abq\,i$ is a homomorphism from the base-changed relative group law of $hD$ to that of $hD_0$ on $T$-points; the morphism `pullback.lift (abq 0).1 (abq 1).1` into the fibre product of the two copies is flat and surjective; and a $T$-point $a$ satisfies $a$ followed by $abq\,i$ equal to the identity for both $i$ precisely when $a$ factors as a $T$-point of the torus followed by $\tau$.
--
--   This is the description of the special fibre at $p$ of the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model of $X_0(N_0p)$: an extension of the product of two copies of $\mathrm{Pic}^0$ of $X_0(N_0)_\kappa$, indexed by the two degeneracy components, by a split torus of rank $s-1$ whose character lattice is indexed by the $s$ supersingular crossing points. It is obtained from the general two-glued-smooth-curves results on relative Picard schemes, and is used downstream for the degeneracy pins on the special fibre, for reducedness of the kernel of the restriction pair, and for local quasi-finiteness of multiplication by $N$ on the fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_representsRelSubPic_torus_abq_specialFibre.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.SplitTorus
  ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.exists_representsRelSubPic_torus_abq_specialFibre
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R p) κ]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
    (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
    (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀)

    [IsProper (baseChange (R p) (toBase N₀ p) κ)]
    [IsProper (baseChange (R p) (toBase0 N₀ p) κ)] [SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) κ)]
    [GeometricallyIntegral (baseChange (R p) (toBase0 N₀ p) κ)]

    (ε₀κ : Spec (CommRingCat.of κ) ⟶ fibre0 (N₀ := N₀) (algebraMap (R p) κ))
    (hε₀κ₁ : ε₀κ ≫ pullback.fst _ _ = specMap (R p) κ ≫ ε₀.1) (hε₀κ₂ : ε₀κ ≫ pullback.snd _ _ = 𝟙 _)
    (hε₁ : ε₀κ ≫ 𝔓.comp κ (algebraMap (R p) κ) 0 = sectionFibre 𝔓.εinf (algebraMap (R p) κ)) :

    Nat.card ↥(pullback (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp κ (algebraMap (R p) κ) 1)) =
        Nat.card ↥(ssPlaces p N₀ κ) ∧
    0 < Nat.card ↥(ssPlaces p N₀ κ) ∧

    ∃ (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) κ) (sectionBaseChange κ 𝔓.εinf)) (D.baseChange κ))
      (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf κ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) κ), pullback.condition⟩)).L))
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) κ) (sectionBaseChange κ ε₀)) (D₀.baseChange κ))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) ε₀ κ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) κ), pullback.condition⟩)).L))
      (hε₁' : (sectionBaseChange κ ε₀).1 ≫ 𝔓.comp κ (algebraMap (R p) κ) 0 = (sectionBaseChange κ 𝔓.εinf).1)
      (τ : SchemeHomOver (torusStr κ (Nat.card ↥(ssPlaces p N₀ κ) - 1)) (D.baseChange κ).toBase)
      (abq : Fin 2 → SchemeHomOver (D.baseChange κ).toBase (D₀.baseChange κ).toBase),

      abq 0 = RepresentsRelSubPic.pullbackHom (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp_over κ (algebraMap (R p) κ) 0)
        hε₁' hDκ hD₀κ ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) κ) t (sectionBaseChange κ ε₀))
              (pullback.snd (baseChange (R p) (toBase0 N₀ p) κ) t)
            ((Scheme.Modules.pullback (curveChange (𝔓.comp κ (algebraMap (R p) κ) 1)
              (𝔓.comp_over κ (algebraMap (R p) κ) 1) t)).obj (hDκ.poincare.pullbackAlong a).L))) ∧

      IsClosedImmersion τ.1 ∧
      (∀ χ χ' : WithConv (torusCoord κ (Nat.card ↥(ssPlaces p N₀ κ) - 1) →ₐ[κ] κ),
        NeronModelInfra.schemeHomOverComp (torusPtId κ (Nat.card ↥(ssPlaces p N₀ κ) - 1) (χ * χ').ofConv) τ =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (specMap (R p) κ)).mul _
            (NeronModelInfra.schemeHomOverComp (torusPtId κ (Nat.card ↥(ssPlaces p N₀ κ) - 1) χ.ofConv) τ)
            (NeronModelInfra.schemeHomOverComp (torusPtId κ (Nat.card ↥(ssPlaces p N₀ κ) - 1) χ'.ofConv) τ)) ∧

      (∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a b : SchemeHomOver t (D.baseChange κ).toBase),
        NeronModelInfra.schemeHomOverComp
            (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (specMap (R p) κ)).mul t a b)
            (abq i) =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (R p) κ)).mul t
            (NeronModelInfra.schemeHomOverComp a (abq i)) (NeronModelInfra.schemeHomOverComp b (abq i))) ∧

      Flat (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) ∧
      Surjective (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D.baseChange κ).toBase),
        (∀ i, NeronModelInfra.schemeHomOverComp a (abq i) =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (R p) κ)).one t) ↔
          ∃ y : SchemeHomOver t (torusStr κ (Nat.card ↥(ssPlaces p N₀ κ) - 1)),
            NeronModelInfra.schemeHomOverComp y τ = a) := by sorry
