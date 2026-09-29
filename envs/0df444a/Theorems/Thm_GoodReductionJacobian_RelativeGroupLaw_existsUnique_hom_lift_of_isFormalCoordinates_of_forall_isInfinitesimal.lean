-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_hom_lift_of_isFormalCoordinates_of_forall_isInfinitesimal
-- name    : GoodReductionJacobian.RelativeGroupLaw.existsUnique_hom_lift_of_isFormalCoordinates_of_forall_isInfinitesimal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/c172ecc8-e0e7-595f-a1c6-2fa0976c378c
-- title:
--   Unique lifting of homomorphisms across a nilpotent thickening
-- statement:
--   Fix a prime $q$, a Noetherian commutative ring $B$ and a $B$-algebra $B_0$ whose structure map $B \to B_0$ is surjective with nilpotent kernel, and assume the image of $q$ in $B$ is nilpotent. Let $f : A \to \operatorname{Spec} B$ and $f' : A' \to \operatorname{Spec} B$ carry relative group laws $L, L'$ (functorial multiplication, unit, inverse on points over a base, natural in the base) which are commutative and satisfy `AbelianSchemePropertyBundle`, i.e. $f$, respectively $f'$, is smooth and proper with connected fibres and admits a relative group law. Let $F, F'$ be $2$-dimensional formal group laws over $B$ and $\theta, \theta'$ systems of formal coordinates for $f$, respectively $f'$: for each $B$-algebra $B'$ a map from $(\operatorname{Fin} 2 \to B')$ to points of $A$ over $\operatorname{Spec} B'$, assumed to be `IsFormalCoordinates` for $L$ and $F$, respectively $L'$ and $F'$ — compatible with $B$-algebra maps on nilpotent tuples and, for every ideal $J$ of $B'$ with $J^{n+1} = \bot$, restricting to a bijection from tuples with entries in $J$ onto the points infinitesimal along $J$ (those whose reduction modulo $J$ is the unit), transporting the truncated formal multiplication $F$.`nilMul` to $L$. It is assumed that $q$-power torsion is infinitesimal on both sides: for every $B$-algebra $C$, every $m$ and every point $P$ of $A$, respectively $A'$, over $\operatorname{Spec} C$ with $q^m \cdot P$ equal to the unit, there is a nilpotent ideal $J \subseteq C$ with $P$ infinitesimal along $J$. Let $f_0 : A_0 \to \operatorname{Spec} B_0$ and $f_0' : A_0' \to \operatorname{Spec} B_0$ carry relative group laws $L_0, L_0'$ and let $g : A_0 \to A$, $g' : A_0' \to A'$ exhibit $f_0, f_0'$ as the base changes of $f, f'$ along $\operatorname{Spec} B_0 \to \operatorname{Spec} B$, compatibly with the multiplications on points. Let $\varphi_0 : A_0 \to A_0'$ be a morphism over $\operatorname{Spec} B_0$ commuting with the multiplications, and let $T$ be a homomorphism $F \to F'$ of formal group laws such that for every ring $B''$ that is an algebra over both $B$ and $B_0$ in a scalar tower, every ideal $J$ with $J^{n+1} = \bot$, every tuple $s$ with entries in $J$ and every point $p_0$ of $A_0$ over $\operatorname{Spec} B''$ with $p_0$ followed by $g$ equal to $\theta\, B''\, s$, the composite of $p_0$, $\varphi_0$ and $g'$ equals $\theta'\, B''$ evaluated at the truncated evaluations $\operatorname{nilEval} n (T_i)(s)$. The conclusion: there is exactly one morphism $\varphi : A \to A'$ such that $g$ followed by $\varphi$ equals $\varphi_0$ followed by $g'$ and, for some proof that $\varphi$ lies over $\operatorname{Spec} B$, the induced map on points over any base is multiplicative for $L$ and $L'$, and for every $B$-algebra $B''$, every ideal $J$ with $J^{n+1} = \bot$ and every tuple $s$ with entries in $J$, the point $\theta\, B''\, s$ followed by $\varphi$ equals $\theta'\, B''$ at $\operatorname{nilEval} n (T_i)(s)$.
--
--   This is the Serre–Tate type rigidity statement in the form used here: over a nilpotent thickening $B \to B_0$ in which $q$ is nilpotent, a homomorphism of the reductions together with a compatible homomorphism of the $2$-dimensional formal groups determines a unique homomorphism upstairs, provided $q$-power torsion is infinitesimal. It is the bare (group-law only) version from which the isomorphism variant [`GoodReductionJacobian.RelativeGroupLaw.existsUnique_iso_lift_of_isFormalCoordinates_of_forall_isInfinitesimal`](thm.html#GoodReductionJacobian.RelativeGroupLaw.existsUnique_iso_lift_of_isFormalCoordinates_of_forall_isInfinitesimal) and the construction of quaternionic actions on fake elliptic curves in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_act_of_bareDeformation_of_isFormalCoordinates`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_act_of_bareDeformation_of_isFormalCoordinates) are derived.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_hom_lift_of_isFormalCoordinates_of_forall_isInfinitesimal.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_hom_lift_of_isFormalCoordinates_of_forall_isInfinitesimal
    {q : ℕ} [Fact q.Prime]

    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hq : IsNilpotent ((q : ℕ) : B))

    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of B)) (f' : A' ⟶ Spec (CommRingCat.of B))
    (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f') (hc : L.IsCommutative) (hc' : L'.IsCommutative)
    (hA : AbelianSchemePropertyBundle B f) (hA' : AbelianSchemePropertyBundle B f')

    (F F' : MvFormalGroup 2 B)
    (θ : RelativeGroupLaw.FormalCoordinates f 2) (θ' : RelativeGroupLaw.FormalCoordinates f' 2)
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')

    (hinf : ∀ (C : Type) [CommRing C] [Algebra B C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B) C) f),
      nsmulPt L (Scheme.specOver (𝒪 := B) C) (q ^ m) P = L.one (Scheme.specOver (𝒪 := B) C) →
        ∃ J : Ideal C, IsNilpotent J ∧ L.IsInfinitesimal J P)
    (hinf' : ∀ (C : Type) [CommRing C] [Algebra B C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B) C) f'),
      nsmulPt L' (Scheme.specOver (𝒪 := B) C) (q ^ m) P = L'.one (Scheme.specOver (𝒪 := B) C) →
        ∃ J : Ideal C, IsNilpotent J ∧ L'.IsInfinitesimal J P)

    {A₀ A₀' : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)) (f₀' : A₀' ⟶ Spec (CommRingCat.of B₀))
    (L₀ : RelativeGroupLaw B₀ f₀) (L₀' : RelativeGroupLaw B₀ f₀')
    (g : A₀ ⟶ A) (g' : A₀' ⟶ A')
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (hg' : IsPullback g' f₀' f' (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (hgmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ g =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg'mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀'),
      (L₀'.mul t P Q).1 ≫ g' =
        (L'.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
          ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1)

    (φ₀ : A₀ ⟶ A₀') (hφ₀ : φ₀ ≫ f₀' = f₀)
    (φ₀_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
      mapPt φ₀ hφ₀ (L₀.mul t P Q) = L₀'.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q))

    (T : MvFormalGroup.Hom F F')
    (hTφ₀ : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''] [IsScalarTower B B₀ B'']
      (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ → ∀ (s : Fin 2 → B''), (∀ i, s i ∈ J) →
      ∀ p₀ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) B'') f₀, p₀.1 ≫ g = (θ B'' s).1 →
        p₀.1 ≫ φ₀ ≫ g' = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toPowerSeries i) s)).1) :
    ∃! φ : A ⟶ A', g ≫ φ = φ₀ ≫ g' ∧
      ∃ hφ : φ ≫ f' = f,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
          mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            (θ B'' s).1 ≫ φ = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toPowerSeries i) s)).1) := by sorry
