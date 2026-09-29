-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
-- name    : ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7ebecea7-70c2-5b84-95bf-981986a2ca78
-- title:
--   Restricting a rigidified section twist to the geometric generic fibre
-- statement:
--   Fix $N_0, p \in \mathbb N$ with $N_0 \neq 0$ and $p$ prime, $p \nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel N₀ p hpN₀`, so that the structure morphism `toBase N₀ p` from the Igusa-type model $X(N_0,p)$ to $\operatorname{Spec} R_p$ ($R_p = \mathbb Z$ localised at $p$) is assumed proper. Let $D$ be a `RelativePic0Designation`, i.e. a scheme $P$ with a morphism $D.\mathrm{toBase} : P \to \operatorname{Spec} R_p$ and a section $D.\mathrm{zeroSection}$, and let $h_D$ witness that $D$ represents the subfunctor, cut out by `algEquivZeroCut`, of line bundles on $X \times_{R_p} T$ rigidified along the section $\mathfrak P.\varepsilon_{\mathrm{inf}}$ whose pullbacks to all geometric fibres are algebraically equivalent to zero; $h_D.\mathrm{poincare}$ is the resulting rigidified Poincaré bundle over $D.\mathrm{toBase}$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ and $\rho : R_p \to A$ a ring homomorphism compatible with the structure map $R_p \to \overline{\mathbb Q}$. Let $s_1,\dots,s_n$ be $A$-points of $X$ over $\operatorname{Spec}\rho$ whose images lie in $\mathfrak P.\mathrm{smoothLocus}$, and let $x_1,\dots,x_n$ be $\overline{\mathbb Q}$-points of $X$ over `genPt p` obtained from them by composition with $\operatorname{Spec} (A \hookrightarrow \overline{\mathbb Q})$. Let $\mathrm{pos},\mathrm{neg} : \mathrm{Fin}\, n \to \mathbb N$. Assume $a$ is an $A$-point of $P$ over $\operatorname{Spec}\rho$ such that the pullback of the Poincaré bundle along $a$ has underlying module isomorphic to the `rigidify` of the twist $\bigotimes_i \mathcal I(s_i)^{\mathrm{pos}_i\,\vee} \otimes \mathcal I(s_i)^{\mathrm{neg}_i}$ (formed by a right fold over $\mathrm{Fin}\,n$ starting from the unit, with $\mathcal I(s_i)$ the ideal sheaf of the graph of $s_i$, a relative effective Cartier divisor of degree one, `invModule` for the positive part and `module` for the negative part), rigidified by tensoring with the pullback along $\mathrm{pullback.snd}$ of the dual of the restriction along $\mathrm{rigSection}$ attached to $\mathfrak P.\varepsilon_{\mathrm{inf}}$. Let $b$ be the $\overline{\mathbb Q}$-point of $P$ obtained from $a$ by the same composition. Then the underlying module of the pullback of the Poincaré bundle along $b$ is isomorphic to the corresponding twist $\bigotimes_i \mathcal I(x_i)^{\mathrm{pos}_i\,\vee} \otimes \mathcal I(x_i)^{\mathrm{neg}_i}$ on $X \times_{R_p} \operatorname{Spec} \overline{\mathbb Q}$, with no rigidifying factor.
--
--   This is the base-change step which transports, from an $A$-point to the geometric generic point, the identification of the Poincaré bundle restricted along a point of the relative $\mathrm{Pic}^0$-representing scheme with a twist by the sections $s_i$: over a field the rigidifying factor, being pulled back from the base, drops out. It is used in the identification of the point of the relative Picard object attached to a divisor supported in the smooth locus with the corresponding divisor class on the geometric generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
    (hsm : ∀ i, Set.range (s i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)))

    (x : Fin n → SchemeHomOver (genPt p) (toBase N₀ p))
    (hx : ∀ i, (x i).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ (s i).1)
    (pos neg : Fin n → ℕ)

    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (ha : Nonempty ((hD.poincare.pullbackAlong a).L ≅
        Scheme.Modules.rigidify (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf)
          (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)))
          ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules))))

    (b : SchemeHomOver (genPt p) D.toBase) (hb : b.1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ a.1) :
    Nonempty ((hD.poincare.pullbackAlong b).L ≅
      ((List.finRange n).foldr
          (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I ^ (pos i)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (toBase N₀ p) (x i).1 (x i).2).I ^ (neg i)).module ⊗ M)
          (𝟙_ (pullback (toBase N₀ p) (genPt p)).Modules))) := by sorry
