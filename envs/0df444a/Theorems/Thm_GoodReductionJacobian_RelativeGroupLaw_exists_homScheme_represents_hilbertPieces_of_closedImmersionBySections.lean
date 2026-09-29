-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/2391cceb-65f9-5dcc-b8cc-7f65d707819a
-- title:
--   Hom-scheme of abelian schemes with Hilbert-polynomial pieces
-- statement:
--   Let $S$ be a commutative ring and let $f : A \to \operatorname{Spec} S$, $g : B \to \operatorname{Spec} S$ be morphisms of schemes (universe $0$) carrying relative group laws $L_A$, $L_B$ — functorial group structures on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for $t : T \to \operatorname{Spec} S$, compatible with precomposition — which are assumed commutative, and such that $f$ and $g$ each satisfy `AbelianSchemePropertyBundle`: smooth, proper, with connected fibres over every point, and admitting some relative group law. Assume further given modules $\mathcal L_A$ on $A$ and $\mathcal L_B$ on $B$ that are invertible (locally isomorphic to the unit) and satisfy `ClosedImmersionBySections`: for some $N$ there is a `ProjPresentation` over $\operatorname{Spec} S$, i.e. sections $\sigma_0,\dots,\sigma_N$ together with a morphism to $\mathbb P^N_S$ over $\operatorname{Spec} S$ framing the module on the basic opens, whose structural morphism to $\operatorname{Proj}$ is a closed immersion. Then there exist a scheme $H$, a morphism $\pi_H : H \to \operatorname{Spec} S$ and an assignment $\mathrm{pt}$ sending each commutative ring $S'$, each $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and each $\varphi : A \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to B$ with $\varphi \circ g$ equal to the second projection followed by $s$ to a morphism $\operatorname{Spec} S' \to H$ over $\operatorname{Spec} S$, with the following properties. (i) Naturality: for a ring map $\psi : S' \to S''$ with $\operatorname{Spec}\psi$ followed by $s$ equal to $s''$, the point attached to the base change of $\varphi$ along $\psi$ is $\operatorname{Spec}\psi$ followed by the point attached to $\varphi$. (ii) Every $x : \operatorname{Spec} S' \to H$ over $\operatorname{Spec} S$ equals $\mathrm{pt}(\varphi)$ for some $\varphi$ as above which is a homomorphism for the group laws, in the sense that for all schemes $T$, all $t' : T \to \operatorname{Spec} S'$ and all $T$-points $P, Q$ of $A$ over $t' \circ s$, the point $L_A.\mathrm{mul}(P,Q)$ composed with $\varphi$ equals $L_B.\mathrm{mul}$ of the composites of $P$ and $Q$ with $\varphi$. (iii) Two such homomorphisms $\varphi, \varphi'$ with the same attached point coincide. (iv) $\pi_H$ is separated, locally of finite type, locally of finite presentation and formally unramified. (v) For every $P \in \mathbb Q[t]$ there is an open $U \subseteq H$ whose underlying set is closed and with the inclusion followed by $\pi_H$ quasi-compact, such that for every $S'$, $s$ and every homomorphism $\varphi$ as in (ii), the set-theoretic image of $\mathrm{pt}(\varphi)$ lies in $U$ if and only if for every algebraically closed field $k$ and every ring map $sk : S' \to k$ there is $d_0$ with: for all $d \ge d_0$, the $k$-dimension of the global sections of the $d$-th tensor power of $(\text{pullback of } \mathcal L_A \text{ along the first projection}) \otimes (\text{pullback of } \mathcal L_B \text{ along } \varphi)$ on the geometric fibre of the second projection at $sk$ equals $P(d)$.
--
--   This is the representability of the functor of homomorphisms between two abelian schemes by a separated, locally finitely presented, formally unramified Hom-scheme over the base, in the tradition of Grothendieck's Hilbert and Hom schemes, strengthened by a stratification of $H$ into open-and-closed pieces, quasi-compact over the base, cut out by the Hilbert polynomial of the graph with respect to the box product of the two given projective embeddings. It feeds the construction of schemes of degree-$e$ homomorphisms and of lattice-action data used in the Čerednik–Drinfeld part of the development, and is the source of the Hom-scheme existence statement with finite presentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MonoidalCategory

theorem GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections
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
      IsSeparated πH ∧ LocallyOfFiniteType πH ∧ LocallyOfFinitePresentation πH ∧ FormallyUnramified πH ∧

      (∀ Pℚ : Polynomial ℚ, ∃ U : H.Opens, IsClosed (U : Set H) ∧ QuasiCompact (U.ι ≫ πH) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
          (Set.range (pt S' s φ hφ).1.base ⊆ (U : Set H) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
                (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
                  (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛A ⊗ (Scheme.Modules.pullback φ).obj 𝓛B)) d) k sk : ℕ) : ℚ) = Pℚ.eval (d : ℚ))) := by sorry
