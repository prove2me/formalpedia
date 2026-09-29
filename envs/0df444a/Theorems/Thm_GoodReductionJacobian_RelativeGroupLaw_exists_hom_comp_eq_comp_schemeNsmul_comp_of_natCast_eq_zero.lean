-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/e1ea2edb-4004-5a4e-9d29-42ad33fef906
-- title:
--   Lifting N^μ times a homomorphism of abelian schemes
-- statement:
--   Let $S$ and $S_0$ be commutative rings with $S_0$ an $S$-algebra whose structure map $S \to S_0$ is surjective, let $N$ be a natural number with $N = 0$ in $S$, and let $\mu$ be a natural number such that the $(\mu+1)$-st power of $\ker(S \to S_0)$ is the zero ideal. Let $f : A \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} S$ be morphisms of schemes, each carrying a relative group law ($L$, resp. $L'$): a group structure, natural in $T$, on the sets of sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for morphisms $t : T \to \operatorname{Spec} S$; assume both are commutative, and assume for each of $f, f'$ the bundle of properties: smoothness, properness, connectedness of all fibres of the underlying map of spaces, and existence of a relative group law. Let $f_0 : A_0 \to \operatorname{Spec} S_0$ and $f'_0 : A'_0 \to \operatorname{Spec} S_0$ carry relative group laws $L_0$, $L'_0$, and let $g : A_0 \to A$, $g' : A'_0 \to A'$ exhibit $A_0$, $A'_0$ as pullbacks of $A$, $A'$ along $\operatorname{Spec} S_0 \to \operatorname{Spec} S$, each compatible with the group laws: composition with $g$ (resp. $g'$) carries $L_0$-products (resp. $L'_0$-products) of sections over $t : T \to \operatorname{Spec} S_0$ to $L$-products (resp. $L'$-products) of the composites over $t$ followed by $\operatorname{Spec} S_0 \to \operatorname{Spec} S$. Finally let $u_0 : A_0 \to A'_0$ satisfy $u_0 \circ f'_0 = f_0$ and carry $L_0$-products of sections to $L'_0$-products of their composites with $u_0$. The conclusion asserts the existence of $F : A \to A'$ with $F \circ f' = f$ which likewise carries $L$-products of sections over any $t : T \to \operatorname{Spec} S$ to $L'$-products of their composites with $F$, and such that $g$ followed by $F$ equals $u_0$ followed by the multiplication-by-$N^{\mu}$ morphism of $A'_0$ (the $N^{\mu}$-fold $L'_0$-multiple of the identity section of $A'_0$ over itself) followed by $g'$.
--
--   This is the infinitesimal lifting statement for homomorphisms of abelian schemes in the form of Katz's Serre–Tate lemma: over a base killed by $N$, a homomorphism between the reductions modulo a nilpotent ideal of nilpotency order $\mu+1$ lifts after multiplication by $N^{\mu}$. It is the form used for the fake elliptic curves of the Čerednik–Drinfel'd part, being cited by the lifting statements for nilpotent and square-zero kernels there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero
    (S S₀ : Type) [CommRing S] [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀))
    (N : ℕ) (hN : (N : S) = 0) (μ : ℕ) (hμ : RingHom.ker (algebraMap S S₀) ^ (μ + 1) = ⊥)

    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f')
    (hc' : L'.IsCommutative) (hA' : AbelianSchemePropertyBundle S f')

    {A₀ : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)) (L₀ : RelativeGroupLaw S₀ f₀)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap S S₀))))
    (hgL : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ g =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {A'₀ : Scheme.{0}} (f'₀ : A'₀ ⟶ Spec (CommRingCat.of S₀)) (L'₀ : RelativeGroupLaw S₀ f'₀)
    (g' : A'₀ ⟶ A') (hg' : IsPullback g' f'₀ f' (Spec.map (CommRingCat.ofHom (algebraMap S S₀))))
    (hg'L : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f'₀),
      (L'₀.mul t P Q).1 ≫ g' =
        (L'.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)))
          ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1)

    (u₀ : A₀ ⟶ A'₀) (hu₀ : u₀ ≫ f'₀ = f₀)
    (hu₀hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ u₀ =
        (L'₀.mul t ⟨P.1 ≫ u₀, by rw [Category.assoc, hu₀]; exact P.2⟩
          ⟨Q.1 ≫ u₀, by rw [Category.assoc, hu₀]; exact Q.2⟩).1) :
    ∃ (F : A ⟶ A') (hF : F ≫ f' = f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
        (L.mul t P Q).1 ≫ F =
          (L'.mul t ⟨P.1 ≫ F, by rw [Category.assoc, hF]; exact P.2⟩
            ⟨Q.1 ≫ F, by rw [Category.assoc, hF]; exact Q.2⟩).1) ∧
      g ≫ F = u₀ ≫ L'₀.schemeNsmul (N ^ μ) ≫ g' := by sorry
