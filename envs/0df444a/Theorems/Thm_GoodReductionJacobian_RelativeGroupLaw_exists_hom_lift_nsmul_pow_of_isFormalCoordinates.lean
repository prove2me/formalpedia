-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_lift_nsmul_pow_of_isFormalCoordinates
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_hom_lift_nsmul_pow_of_isFormalCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/2d23c7dc-1b47-58e4-a2f3-d303e25c9f50
-- title:
--   Lifting q^{nμ}φ₀ to a homomorphism over B
-- statement:
--   Fix a prime $q$, a Noetherian commutative ring $B$ and a commutative $B$-algebra $B_0$ whose structure map $B \to B_0$ is surjective, with $\mu$ such that the $(\mu+1)$-st power of $\ker(B \to B_0)$ vanishes, and $n$ such that $q^n = 0$ in $B$. Over $\operatorname{Spec} B$ are given two schemes $f : A \to \operatorname{Spec} B$, $f' : A' \to \operatorname{Spec} B$, each equipped with a relative group law (a functorial group structure on the sets of points over a $B$-scheme, natural in the base) that is commutative, and each satisfying the bundle of properties `AbelianSchemePropertyBundle`: smooth, proper, connected fibres, and admitting a relative group law. Further data: two-dimensional formal group laws $F$, $F'$ over $B$ and formal coordinate systems $\theta$, $\theta'$ for $f$, $f'$, i.e. assignments sending a tuple in a $B$-algebra $B'$ to a $B'$-point, such that $\theta$ (resp. $\theta'$) is compatible with $B$-algebra maps on nilpotent tuples and, for every ideal $J$ of a $B$-algebra $B'$ with $J^{k+1} = 0$, restricts to a bijection from $J$-valued tuples onto the points congruent to the identity modulo $J$ which transforms the $k$-truncated addition law of $F$ (resp. $F'$) into the group law. Over $B_0$ are given $f_0 : A_0 \to \operatorname{Spec} B_0$ and $f_0' : A_0' \to \operatorname{Spec} B_0$ with relative group laws $L_0$, $L_0'$, together with morphisms $g : A_0 \to A$ and $g' : A_0' \to A'$ making the squares over $\operatorname{Spec} B_0 \to \operatorname{Spec} B$ cartesian and carrying products of points to products of the transported points; a morphism $\varphi_0 : A_0 \to A_0'$ over $B_0$ that is additive on points; and a homomorphism $T : F \to F'$ of formal group laws (a pair of power series without constant term satisfying the substitution identity). The last hypothesis says that $T$ computes $\varphi_0$ infinitesimally: for every ring $B''$ that is a $B$-algebra and a $B_0$-algebra compatibly, every ideal $J$ with $J^{m+1} = 0$, every tuple $s$ with entries in $J$ and every point $p_0$ of $A_0$ over $B''$ with $p_0$ followed by $g$ equal to $\theta(s)$, the composite of $p_0$, $\varphi_0$ and $g'$ equals $\theta'$ evaluated at the truncated values $\operatorname{nilEval}_m(T_i, s)$. The conclusion asserts the existence of a morphism $\tilde N : A \to A'$ over $B$ which (i) is a homomorphism for the two group laws on all points, (ii) satisfies, for every point $P$ of $A_0$ over a $B_0$-scheme, that $P$ followed by $g$ and $\tilde N$ equals the $q^{n\mu}$-fold $L_0'$-multiple of $\varphi_0 \circ P$ followed by $g'$, and (iii) satisfies, for every $B$-algebra $B''$, ideal $J$ with $J^{k+1} = 0$ and tuple $s$ with entries in $J$, that $\theta(s)$ followed by $\tilde N$ equals $\theta'$ evaluated at the $k$-truncations of the series obtained by substituting $T$ into the multiplication-by-$q^{n\mu}$ series of $F'$.
--
--   This is the morphism-level form of Katz's $N$-trick in Serre–Tate theory: a homomorphism between the reductions need not lift, but its $q^{n\mu}$-fold multiple does, and the lift is pinned down both on the reduction and on infinitesimal points in formal coordinates. It feeds the uniqueness-and-existence statement [`GoodReductionJacobian.RelativeGroupLaw.existsUnique_hom_lift_of_isFormalCoordinates_of_forall_isInfinitesimal`](thm.html#GoodReductionJacobian.RelativeGroupLaw.existsUnique_hom_lift_of_isFormalCoordinates_of_forall_isInfinitesimal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_lift_nsmul_pow_of_isFormalCoordinates.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hom_lift_nsmul_pow_of_isFormalCoordinates
    {q : ℕ} [Fact q.Prime]

    (B B₀ : Type) [CommRing B] [IsNoetherianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀))
    (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥) (n : ℕ) (hn : ((q : ℕ) : B) ^ n = 0)

    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of B)) (f' : A' ⟶ Spec (CommRingCat.of B))
    (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f') (hc : L.IsCommutative) (hc' : L'.IsCommutative)
    (hA : AbelianSchemePropertyBundle B f) (hA' : AbelianSchemePropertyBundle B f')

    (F F' : MvFormalGroup 2 B)
    (θ : RelativeGroupLaw.FormalCoordinates f 2) (θ' : RelativeGroupLaw.FormalCoordinates f' 2)
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')

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
    ∃ (Ñ : A ⟶ A') (hÑ : Ñ ≫ f' = f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
        mapPt Ñ hÑ (L.mul t P Q) = L'.mul t (mapPt Ñ hÑ P) (mapPt Ñ hÑ Q)) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t f₀),
        P.1 ≫ g ≫ Ñ = (nsmulPt L₀' t (q ^ (n * μ)) (mapPt φ₀ hφ₀ P)).1 ≫ g') ∧

      (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (k : ℕ), J ^ (k + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ Ñ =
            (θ' B'' (fun i => MvFormalGroup.nilEval k
              (MvPowerSeries.subst T.toPowerSeries (F'.nthSeries (q ^ (n * μ)) i)) s)).1) := by sorry
