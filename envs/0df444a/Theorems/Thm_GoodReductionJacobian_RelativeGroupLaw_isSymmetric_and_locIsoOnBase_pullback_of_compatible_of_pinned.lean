-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isSymmetric_and_locIsoOnBase_pullback_of_compatible_of_pinned
-- name    : GoodReductionJacobian.RelativeGroupLaw.isSymmetric_and_locIsoOnBase_pullback_of_compatible_of_pinned
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/c313bdf6-881a-52f2-86df-865e5124856b
-- title:
--   Symmetry and the square relation under compatible base change
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme with a morphism $f \colon A \to \operatorname{Spec} S$, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi \colon T \to A : \varphi \circ f = t\}$ of $A$-points over morphisms $t \colon T \to \operatorname{Spec} S$, compatible with precomposition. Let $\mathcal L$ be an $\mathcal O_A$-module, let $X$ and $Y$ be commutative $S$-algebras, and let $\varphi \colon X \to Y$ be a ring homomorphism with $\varphi \circ (S \to X) = (S \to Y)$. Write $A_X$ and $A_Y$ for the pullbacks of $f$ along $\operatorname{Spec}$ of the structure maps, with projections $\mathrm{pr}_1$, $\mathrm{pr}_2$. Assume given relative group laws $L_X$ on $\mathrm{pr}_2 \colon A_X \to \operatorname{Spec} X$ and $L_Y$ on $\mathrm{pr}_2 \colon A_Y \to \operatorname{Spec} Y$ which are compatible with $L$, in the sense that for all test schemes and all pairs of points the first projection of the $L_X$- (resp. $L_Y$-) product equals the $L$-product of the projected points; assume given $\rho \colon A_Y \to A_X$ pinned by $\rho \circ \mathrm{pr}_1 = \mathrm{pr}_1$ and $\rho \circ \mathrm{pr}_2 = \operatorname{Spec}(\varphi) \circ \mathrm{pr}_2$; and let $\mathcal M$ be an invertible module on $A_X$, meaning every point has an open neighbourhood on which $\mathcal M$ restricts to an isomorph of the unit module. The conclusion is a threefold statement: $\rho^*\mathcal M$ is invertible; if $[-1]_{L_X}^*\mathcal M$ and $\mathcal M$ are locally isomorphic over the base (for every point of $\operatorname{Spec} X$ there is an open neighbourhood $U$ with the two modules isomorphic after restriction to $\mathrm{pr}_2^{-1}(U)$), then $[-1]_{L_Y}^*\rho^*\mathcal M$ and $\rho^*\mathcal M$ are locally isomorphic over $\operatorname{Spec} Y$ in the same sense; and if $\mathrm{pr}_1^*\mathcal L$ is locally isomorphic over $\operatorname{Spec} X$ to $\mathcal M \otimes [-1]_{L_X}^*\mathcal M$, then $\mathrm{pr}_1^*\mathcal L$ is locally isomorphic over $\operatorname{Spec} Y$ to $\rho^*\mathcal M \otimes [-1]_{L_Y}^*\rho^*\mathcal M$. Here $[-1]_{L}$ denotes the morphism underlying the $L$-inverse of the identity point.
--
--   This records the stability under compatible base change of the two conditions that enter the notion of a symmetric invertible module and of a square root of a given module in the relative Picard setting: symmetry under the inversion morphism, and the local identification of $\mathcal L$ with $\mathcal M \otimes [-1]^*\mathcal M$. It is used in the construction of a symmetric square root of a line bundle on the Néron-model/abelian-scheme side, where the base is replaced by a localisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isSymmetric_and_locIsoOnBase_pullback_of_compatible_of_pinned.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.RelativeGroupLaw.isSymmetric_and_locIsoOnBase_pullback_of_compatible_of_pinned
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    (X Y : Type) [CommRing X] [CommRing Y] [Algebra S X] [Algebra S Y]
    (φ : X →+* Y) (hφ : φ.comp (algebraMap S X) = algebraMap S Y)
    (LX : RelativeGroupLaw X (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))))
    (hLX : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of X))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))))),
        (LX.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S X)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (LY : RelativeGroupLaw Y (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))))
    (hLY : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of Y))
        (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))),
        (LY.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S Y)))
            ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))),
              by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (ρ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
    (hρ₁ : ρ ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
    (hρ₂ : ρ ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))) = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))) ≫ Spec.map (CommRingCat.ofHom φ))
    (𝓜 : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S X)))).Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback ρ).obj 𝓜) ∧
    (IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) LX 𝓜 →
      IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) LY ((Scheme.Modules.pullback ρ).obj 𝓜)) ∧
    (LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S X))))).obj 𝓛)
        (𝓜 ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S X)))) LX)).obj 𝓜) →
      LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S Y))))).obj 𝓛)
        ((Scheme.Modules.pullback ρ).obj 𝓜 ⊗
          (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S Y)))) LY)).obj ((Scheme.Modules.pullback ρ).obj 𝓜))) := by sorry
