-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_pullback_fst_snd_mul_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/e3c62db3-e9ec-5d03-8b97-c98a8cdab356
-- title:
--   Product relative group law on A×_R A
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme, $f \colon A \to \operatorname{Spec} R$ a morphism, and let $L$ be a relative group law on $f$ in the sense of `RelativeGroupLaw`: a functorial group structure (multiplication, unit, inverse, associativity, unit and inverse laws, and naturality under base change of the test object) on the sets $\mathrm{SchemeHomOver}\ t\ f = \{\varphi \colon S \to A \mid \varphi \circ f = t\}$ of $S$-points of $A$ over $t \colon S \to \operatorname{Spec} R$. The assertion is that there exists a relative group law $L_P$ on the composite $\mathrm{pullback.fst}\,f\,f$ followed by $f$, the structural morphism $A \times_{\operatorname{Spec} R} A \to \operatorname{Spec} R$, with the following four compatibilities. First, for every $t \colon S \to \operatorname{Spec} R$ and all points $P, Q$ of the fibre product over $t$, the underlying morphism of $L_P.\mathrm{mul}\ t\ P\ Q$ composed with the first projection equals the $L$-product of $P$ and $Q$ composed with the first projection (the composites being points of $A$ over $t$ by associativity). Second, the same identity for the second projection, where the required compatibility uses `pullback.condition`. Third, the unit of $L_P$ over $t$ has both projections equal to the unit $L.\mathrm{one}\ t$. Fourth, if $L$ is commutative, i.e. $L.\mathrm{mul}$ is symmetric for every test object, then the morphism $\mu \colon A \times_{\operatorname{Spec} R} A \to A$ obtained as the $L$-product of the two projections, viewed as points over $\mathrm{pullback.fst}\,f\,f \gg f$, satisfies $\mu \circ (L_P.\mathrm{mul}\ t\ P\ Q) = (\mu \circ P) \cdot_L (\mu \circ Q)$. Only existence is claimed; no uniqueness of $L_P$ is asserted, and no constraint is placed on $L_P.\mathrm{inv}$.
--
--   This is the standard product group law on the self-fibre-product of a relative group scheme, for which both projections are homomorphisms and the unit is the diagonal unit, together with the observation that the multiplication morphism $\mu$ itself is a homomorphism exactly in the commutative case. It is used in the construction of the two-cocycle obstruction attached to an abelian scheme property bundle, where differences of pullbacks along $\mu$, $\mathrm{fst}$ and $\mathrm{snd}$ are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_pullback_fst_snd_mul_hom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_pullback_fst_snd_mul_hom
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) :
    ∃ LP : RelativeGroupLaw R (pullback.fst f f ≫ f),

      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.fst f f ≫ f)),
          (LP.mul t P Q).1 ≫ pullback.fst f f =
            (L.mul t ⟨P.1 ≫ pullback.fst f f, by rw [Category.assoc]; exact P.2⟩
              ⟨Q.1 ≫ pullback.fst f f, by rw [Category.assoc]; exact Q.2⟩).1) ∧
      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.fst f f ≫ f)),
          (LP.mul t P Q).1 ≫ pullback.snd f f =
            (L.mul t ⟨P.1 ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]; exact P.2⟩
              ⟨Q.1 ≫ pullback.snd f f, by rw [Category.assoc, ← pullback.condition]; exact Q.2⟩).1) ∧

      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)),
          (LP.one t).1 ≫ pullback.fst f f = (L.one t).1 ∧ (LP.one t).1 ≫ pullback.snd f f = (L.one t).1) ∧

      (L.IsCommutative →
        ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (pullback.fst f f ≫ f)),
          (LP.mul t P Q).1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 =
            (L.mul t
              ⟨P.1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1,
                by rw [Category.assoc, (L.mul (pullback.fst f f ≫ f) _ _).2]; exact P.2⟩
              ⟨Q.1 ≫ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1,
                by rw [Category.assoc, (L.mul (pullback.fst f f ≫ f) _ _).2]; exact Q.2⟩).1) := by sorry
