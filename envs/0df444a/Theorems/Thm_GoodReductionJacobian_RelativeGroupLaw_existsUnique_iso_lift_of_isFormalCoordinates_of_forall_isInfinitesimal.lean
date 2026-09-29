-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_iso_lift_of_isFormalCoordinates_of_forall_isInfinitesimal
-- name    : GoodReductionJacobian.RelativeGroupLaw.existsUnique_iso_lift_of_isFormalCoordinates_of_forall_isInfinitesimal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b034d57b-5baa-5ccc-8d13-4391378e0b52
-- title:
--   Serre–Tate lifting of an isomorphism across a nilpotent thickening
-- statement:
--   Let $q$ be a prime, $B$ a Noetherian commutative ring, $B_0$ a commutative $B$-algebra whose structure map $B \to B_0$ is surjective with nilpotent kernel, and suppose $q$ is nilpotent in $B$. Let $f : A \to \operatorname{Spec} B$ and $f' : A' \to \operatorname{Spec} B$ carry relative group laws $L$, $L'$ (functorial group structures on the sets of points over varying $\operatorname{Spec} B$-schemes, natural in the base), both commutative, and let both satisfy `AbelianSchemePropertyBundle`, i.e. be smooth and proper with connected fibres and admit a relative group law. Let $F, F'$ be formal group laws in two variables over $B$ and $\theta, \theta'$ formal coordinates for $f$, $f'$: assignments, to each $B$-algebra $B'$ and each tuple $s \in (B')^{2}$, of a point of $A$ (resp. $A'$) over $\operatorname{Spec} B'$. The hypotheses $L.\mathrm{IsFormalCoordinates}\,F\,\theta$ and its primed analogue say that $\theta$ is compatible with $B$-algebra maps on nilpotent tuples and that, for every ideal $J$ of a $B$-algebra $B'$ with $J^{n+1} = 0$, the tuples with entries in $J$ are carried bijectively onto the points that are $J$-infinitesimal (reduce to the unit section modulo $J$), with $F$'s truncated multiplication going over to $L$'s multiplication. It is further assumed that $q$-power torsion is infinitesimal: for every $B$-algebra $C$, every $m$ and every point $P$ of $A$ over $\operatorname{Spec} C$ with $q^m P$ equal to the unit, some nilpotent ideal $J \subseteq C$ makes $P$ $J$-infinitesimal, and likewise for $A'$. Let $f_0 : A_0 \to \operatorname{Spec} B_0$ and $f_0' : A_0' \to \operatorname{Spec} B_0$ carry relative group laws $L_0$, $L_0'$, and let $g : A_0 \to A$, $g' : A_0' \to A'$ exhibit $A_0$, $A_0'$ as the base changes of $A$, $A'$ along $\operatorname{Spec} B_0 \to \operatorname{Spec} B$ (pullback squares) and be compatible with the group laws on points. Let $e_0 : A_0 \cong A_0'$ be an isomorphism over $\operatorname{Spec} B_0$ ($e_0$ followed by $f_0'$ is $f_0$) which is a homomorphism for $L_0$, $L_0'$ on points over every base. Finally let $T : F \to F'$ be a homomorphism of formal group laws admitting a two-sided inverse $S : F' \to F$ under substitution of power series, and assume $T$ induces $e_0$ on infinitesimal points: whenever $B''$ is simultaneously a $B$- and $B_0$-algebra compatibly, $J \subseteq B''$ an ideal with $J^{n+1} = 0$, $s$ a pair of elements of $J$, and $p_0$ a point of $A_0$ over $\operatorname{Spec} B''$ whose image under $g$ is $\theta(s)$, then $p_0$ followed by $e_0$ and $g'$ is the point $\theta'$ of the tuple obtained by evaluating the degree-$n$ truncations of the components of $T$ at $s$. The conclusion is that there is exactly one isomorphism $e : A \cong A'$ such that $g$ followed by $e$ equals $e_0$ followed by $g'$ and such that $e$ is a morphism over $\operatorname{Spec} B$ which is a homomorphism for $L$, $L'$ on points over every base and satisfies $\theta(s)$ followed by $e$ equals $\theta'$ evaluated at the truncations of $T$ applied to $s$, for every $B$-algebra $B''$, every ideal $J$ with $J^{n+1} = 0$ and every pair $s$ of elements of $J$.
--
--   This is the rigidity (full faithfulness) step of Serre–Tate theory in the form needed here: over a nilpotent thickening $B \to B_0$ in which a prime $q$ is nilpotent, an isomorphism of the reductions together with a compatible isomorphism of the associated two-dimensional formal groups determines a unique isomorphism of the abelian schemes themselves, the $q$-power torsion being assumed infinitesimal in place of an appeal to a divisible-group structure. It is used in the construction of formal coordinates lifting given ones for bare deformations, via [`GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot), and is the group-law-only counterpart of the corresponding statement for quaternionic data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_iso_lift_of_isFormalCoordinates_of_forall_isInfinitesimal.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_iso_lift_of_isFormalCoordinates_of_forall_isInfinitesimal
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

    (e₀ : A₀ ≅ A₀') (he₀f : e₀.hom ≫ f₀' = f₀)
    (he₀mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
      mapPt e₀.hom he₀f (L₀.mul t P Q) = L₀'.mul t (mapPt e₀.hom he₀f P) (mapPt e₀.hom he₀f Q))

    (T : MvFormalGroup.Hom F F')
    (hT : ∃ S : MvFormalGroup.Hom F' F,
      Series.comp S.toPowerSeries T.toPowerSeries = Series.id B ∧ Series.comp T.toPowerSeries S.toPowerSeries = Series.id B)
    (hTe₀ : ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B₀ B''] [IsScalarTower B B₀ B'']
      (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ → ∀ (s : Fin 2 → B''), (∀ i, s i ∈ J) →
      ∀ p₀ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) B'') f₀, p₀.1 ≫ g = (θ B'' s).1 →
        p₀.1 ≫ e₀.hom ≫ g' = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toPowerSeries i) s)).1) :
    ∃! e : A ≅ A', g ≫ e.hom = e₀.hom ≫ g' ∧
      ∃ he : e.hom ≫ f' = f,
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
          mapPt e.hom he (L.mul t P Q) = L'.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
            (θ B'' s).1 ≫ e.hom = (θ' B'' (fun i => MvFormalGroup.nilEval n (T.toPowerSeries i) s)).1) := by sorry
