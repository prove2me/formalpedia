-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isAlgEquivZero_fibre_ofInvertible_of_pullback_zeroSection_iso_unit_of_charP
-- name    : ModularCurve.DRModelPackageLevel.isAlgEquivZero_fibre_ofInvertible_of_pullback_zeroSection_iso_unit_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/98252c97-f2da-55a8-868d-103354ec3abf
-- title:
--   Characteristic-p fibres of the rigidified bundle lie in Pic⁰
-- statement:
--   Fix $N_0 \ge 1$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak P$ be a Deligne–Rapoport model package at level $N_0p$ for the Igusa structure morphism $c =$ `toBase N₀ p` from $X(N_0p)$ to $\operatorname{Spec}(R_p)$, with distinguished section $\mathfrak P.\varepsilon_{\infty}$ of $c$ over the identity. Let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}(R_p)$, locally of finite type, together with a section $D.\mathrm{zeroSection}$, and suppose $D$ represents the relative sub-Picard condition `algEquivZeroCut`: there is a rigidified line bundle on $X \times_{R_p} D.P$ (rigidified along $\varepsilon_\infty$) satisfying `FibrewiseAlgEquivZero`, it is universal for rigidified line bundles with that property on arbitrary bases over $R_p$, and its restriction along the zero section is isomorphic to the unit. Let $M$ be a module on $X \times_{R_p} D.P$ that is locally isomorphic to the unit (invertible), and assume the pullback of $M$ along the base change of the zero section, i.e. the restriction of $M$ to $X \times_{R_p} \operatorname{Spec}(R_p)$, is isomorphic to the unit sheaf. Then for every algebraically closed field $k$ of characteristic $p$ and every morphism $s \colon \operatorname{Spec}(k) \to D.P$, the restriction to the fibre $X \times_{R_p} D.P \times_{D.P} \operatorname{Spec}(k)$, viewed over $\operatorname{Spec}(k)$ via `fibreAt`, of the canonically re-rigidified bundle $M \otimes q^{*}(\varepsilon_\infty^{*}M)^{\vee}$ produced by `RigidifiedLineBundle.ofInvertible` (where $q$ is the projection to $D.P$) satisfies `IsAlgEquivZero`: there exist a scheme $T'$ over $k$, locally of finite type and geometrically integral, an invertible module on the fibre $\times_k T'$, and two $k$-sections of $T'$ along which that module restricts to the unit and to the given bundle respectively.
--
--   This is the characteristic-$p$ case of the assertion that a line bundle on $X(N_0p) \times_{R_p} \mathrm{Pic}^0$ trivial along the zero section becomes, after canonical re-rigidification along the cusp $\infty$, fibrewise algebraically equivalent to zero; the geometric fibres in characteristic $p$ are handled through the Deligne–Rapoport description of the special fibre as two Igusa curves glued at the supersingular points. It feeds the fibrewise verification used to norm the pullback of the Poincaré bundle, [`ModularCurve.DRModelPackageLevel.fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare`](thm.html#ModularCurve.DRModelPackageLevel.fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isAlgEquivZero_fibre_ofInvertible_of_pullback_zeroSection_iso_unit_of_charP.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.isAlgEquivZero_fibre_ofInvertible_of_pullback_zeroSection_iso_unit_of_charP
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    [LocallyOfFiniteType D.toBase]
    (M : (pullback (toBase N₀ p) D.toBase).Modules) (hM : Scheme.Modules.IsInvertible M)

    (h0 : Nonempty ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p)
        (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) D.toBase))).obj M ≅
      SheafOfModules.unit (pullback (toBase N₀ p) (𝟙 (Spec (CommRingCat.of (R p))))).ringCatSheaf)) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (s : Spec (CommRingCat.of k) ⟶ D.P),
      IsAlgEquivZero (fibreAt (toBase N₀ p) D.toBase s)
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd (toBase N₀ p) D.toBase) s)).obj
          (RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf) M hM).L) := by sorry
