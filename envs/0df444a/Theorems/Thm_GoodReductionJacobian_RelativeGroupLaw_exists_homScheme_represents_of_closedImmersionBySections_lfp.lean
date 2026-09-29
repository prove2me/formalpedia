-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_of_closedImmersionBySections_lfp
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_of_closedImmersionBySections_lfp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/e892c9fc-2428-5cbe-9d17-e03225ca68d6
-- title:
--   Existence of a Hom scheme for abelian schemes
-- statement:
--   Let $S$ be a commutative ring, and let $f : A \to \operatorname{Spec} S$ and $g : B \to \operatorname{Spec} S$ be morphisms of schemes (in universe $0$) equipped with relative group laws $L_A$, $L_B$, that is, functorial group structures on the sets of sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for $t : T \to \operatorname{Spec} S$ (multiplication, unit, inverse, associativity, unit and inverse laws, and compatibility of multiplication with precomposition in $T$), both assumed commutative; assume further that $f$ and $g$ each satisfy `AbelianSchemePropertyBundle`, i.e. are smooth and proper with connected fibres over every point of $\operatorname{Spec} S$ and admit some relative group law. Assume given module sheaves $\mathcal L_A$ on $A$ and $\mathcal L_B$ on $B$ that are invertible (locally isomorphic to the unit sheaf) and satisfy `ClosedImmersionBySections` over $f$, resp. $g$: for some $N$ there is a projective presentation, consisting of $N+1$ global sections, a morphism to $\operatorname{Proj}$ of the polynomial ring in $N+1$ variables over $S$ lying over the structure morphism, together with the framing and ratio compatibilities, whose associated morphism to $\operatorname{Proj}$ is a closed immersion. Then there exist a scheme $H$, a morphism $\pi_H : H \to \operatorname{Spec} S$, and a rule $\mathrm{pt}$ assigning to every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every $\varphi : A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to B$ with $\varphi$ lying over $s$ (i.e. $\varphi \circ g$ equals the second projection followed by $s$) a section of $\pi_H$ over $s$, such that: (i) $\mathrm{pt}$ is natural, in that for a ring homomorphism $\psi : S' \to S''$ with $\operatorname{Spec}\psi$ followed by $s$ equal to $s''$, the underlying morphism of $\mathrm{pt}$ applied to the base change of $\varphi$ along $\psi$ equals $\operatorname{Spec}\psi$ followed by the underlying morphism of $\mathrm{pt}(S', s, \varphi)$; (ii) every section $x$ of $\pi_H$ over $s$ is of the form $\mathrm{pt}(S', s, \varphi)$ for some $\varphi$ over $s$ which is a homomorphism in the pointwise sense, namely for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all sections $P, Q$ of $f$ over $t'$ followed by $s$, the section of $g$ obtained by composing the lift of $L_A$-product of $P$ and $Q$ with $\varphi$ coincides with the $L_B$-product of the sections obtained from $P$ and $Q$ by composing their lifts with $\varphi$; (iii) two such pointwise homomorphisms $\varphi$, $\varphi'$ over the same $s$ with $\mathrm{pt}(S', s, \varphi) = \mathrm{pt}(S', s, \varphi')$ are equal; and (iv) $\pi_H$ is separated, locally of finite type, locally of finite presentation and formally unramified.
--
--   This is the representability of the Hom functor $S' \mapsto \operatorname{Hom}_{S'}(A_{S'}, B_{S'})$ between abelian schemes, on affine base changes, together with the standard finiteness and rigidity properties of the representing scheme. It is used in the construction of fake elliptic curves with quaternionic multiplication, where it supplies relative representability for the existence of an action of a prescribed order on an abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_of_closedImmersionBySections_lfp.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_of_closedImmersionBySections_lfp
    (S : Type) [CommRing S] {A B : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of S)) (g : B ⟶ Spec (CommRingCat.of S))
    (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)
    (hAc : LA.IsCommutative) (hBc : LB.IsCommutative)
    (hA : AbelianSchemePropertyBundle S f) (hB : AbelianSchemePropertyBundle S g)
    (𝓛A : A.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A) (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A f)
    (𝓛B : B.Modules) (hB₁ : Scheme.Modules.IsInvertible 𝓛B) (hB₂ : Scheme.Modules.ClosedImmersionBySections 𝓛B g) :
    ∃ (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : pullback f s ⟶ B), φ ≫ g = pullback.snd f s ≫ s → SchemeHomOver s πH),

      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πH),
        ∃ (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) ∧
          pt S' s φ hφ = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ φ' : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ' =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ') ∧
      IsSeparated πH ∧ LocallyOfFiniteType πH ∧ LocallyOfFinitePresentation πH ∧ FormallyUnramified πH := by sorry
