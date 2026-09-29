-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_mvFormalGroup_kernelOfReduction_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/bb05e17e-cdd0-5fb9-bf99-abfe1cc3a9fb
-- title:
--   Formal group of a smooth commutative relative group law
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism equipped with a relative group law $L$, that is, a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points over each $t : T \to \operatorname{Spec} R$, compatible with base change along $T' \to T$; assume $L$ is commutative and $f$ is smooth. Then there are $n \in \mathbb{N}$ and $a : \mathrm{Fin}\,n \to R$ whose range generates the unit ideal, such that for each $i$ and each $R$-algebra $R_i$ that is a localisation of $R$ away from $a_i$ there exist $g \in \mathbb{N}$, a $g$-dimensional formal group law $F$ over $R_i$ (a $g$-tuple of power series in $2g$ variables with zero constant term, linear part $X_j + Y_j$, and associative under substitution), and maps $\theta_{C,J}$, defined for every $R_i$-algebra $C$ and ideal $J$ with $C$ $J$-adically complete, from the points $F(C,J)$ (tuples $x : \mathrm{Fin}\,g \to C$ with each $x_j$ in the radical of $J$, with addition given by adic evaluation of $F$) to the $C$-points of $A$ over $R$ via $R \to R_i \to C$, such that: $F$ is commutative; and for every such $C,J$ with $J$ nilpotent, $\theta_{C,J}$ is injective, a point $x$ has all coordinates in $J$ precisely when the reduction of $\theta_{C,J}(x)$ along $C \to C/J$ is the unit point of $L$ over $\operatorname{Spec}(C/J)$, every $C$-point of $A$ over $R$ whose reduction modulo $J$ is that unit point lies in the image of $\theta_{C,J}$, $\theta_{C,J}(x+y) = L.\mathrm{mul}$ of $\theta_{C,J}(x)$ and $\theta_{C,J}(y)$, and the $\theta$'s are natural: for an $R_i$-algebra map $\varphi : C \to C'$ with $J'$ nilpotent and $C'$ $J'$-adically complete and $x'_j = \varphi(x_j)$, the point $\theta_{C',J'}(x')$ is $\theta_{C,J}(x)$ precomposed with $\operatorname{Spec}\varphi$. Moreover every endomorphism $u : A \to A$ over $\operatorname{Spec} R$ that respects $L.\mathrm{mul}$ on points over every base is induced, through all the $\theta_{C,J}$ with $J$ nilpotent, by some endomorphism $\rho$ of $F$; and two endomorphisms of $F$ agreeing on $F(C,J)$ for all $C$ and all nilpotent $J$ are equal.
--
--   This is the formal completion of a smooth commutative group scheme along its unit section, produced Zariski-locally on the affine base as an honest $g$-dimensional formal group law together with the dictionary identifying its points with coordinates in a nilpotent ideal $J$ with the kernel of the reduction map $A(C) \to A(C/J)$, and with a faithful action of the endomorphisms of the group law. It is used in the Čerednik–Drinfel'd part of the development, where the formal group attached to a fake elliptic curve and the traces of quaternionic endomorphisms are computed from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem GoodReductionJacobian.RelativeGroupLaw.exists_mvFormalGroup_kernelOfReduction_of_smooth
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hL : L.IsCommutative) (hf : Smooth f) :
    ∃ (n : ℕ) (a : Fin n → R), Ideal.span (Set.range a) = ⊤ ∧
      ∀ (i : Fin n) (Rᵢ : Type u) [CommRing Rᵢ] [Algebra R Rᵢ] [IsLocalization.Away (a i) Rᵢ],
        ∃ (g : ℕ) (F : MvFormalGroup g Rᵢ)
          (θ : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C],
            F.Points C J →
              SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f),
          F.IsComm ∧
          (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →

            Function.Injective (θ C J) ∧

            (∀ x : F.Points C J,
              (∀ j, x.val j ∈ J) ↔
                Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (θ C J x).1 =
                  (L.one (Spec.map (CommRingCat.ofHom
                    ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))))).1) ∧

            (∀ P : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f,
              Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 =
                  (L.one (Spec.map (CommRingCat.ofHom
                    ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))))).1 →
                P ∈ Set.range (θ C J)) ∧

            (∀ x y : F.Points C J,
              θ C J (x + y) =
                L.mul (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ))))
                  (θ C J x) (θ C J y)) ∧

            (∀ (C' : Type u) [CommRing C'] [Algebra Rᵢ C'] (J' : Ideal C') [IsAdicComplete J' C'],
              IsNilpotent J' →
                ∀ (φ : C →ₐ[Rᵢ] C') (x : F.Points C J) (x' : F.Points C' J'),
                  (∀ j, x'.val j = φ (x.val j)) →
                    (θ C' J' x').1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (θ C J x).1)) ∧

          (∀ (u : A ⟶ A) (hu : u ≫ f = f),
            (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
              pushPt u hu (L.mul t P Q) = L.mul t (pushPt u hu P) (pushPt u hu Q)) →
            ∃ ρ : MvFormalGroup.End F,
              ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
                ∀ x : F.Points C J,
                  θ C J (MvFormalGroup.Hom.evalPoints ρ x) = pushPt u hu (θ C J x)) ∧

          (∀ ρ ρ' : MvFormalGroup.End F,
            (∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
              ∀ x : F.Points C J,
                MvFormalGroup.Hom.evalPoints ρ x = MvFormalGroup.Hom.evalPoints ρ' x) → ρ = ρ') := by sorry
