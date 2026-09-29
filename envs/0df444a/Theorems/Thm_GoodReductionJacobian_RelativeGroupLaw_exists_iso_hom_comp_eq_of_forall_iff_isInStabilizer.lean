-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/0de45775-6c52-51b6-92fa-278633b90554
-- title:
--   Sections of a stabiliser subscheme are transitively permuted
-- statement:
--   Let $R$ be a commutative ring, let $A$ and $K$ be schemes, let $f : A \to \operatorname{Spec} R$, and let $L$ be a relative group law on $f$, i.e. a system of operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} R$, satisfying associativity, the two unit laws, left inversion, and naturality of $\mathrm{mul}$ under base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $\mathcal L$ be a sheaf of modules on $A$ and let $\iota : K \to A$ be a monomorphism. Assume that $\iota$ represents the stabiliser of $\mathcal L$ in the following sense: for every $t : T \to \operatorname{Spec} R$ and every point $x = (\varphi, \varphi \circ f = t)$ over $t$, the morphism $\varphi$ factors as some $\kappa : T \to K$ followed by $\iota$ if and only if $x$ lies in the stabiliser of $\mathcal L$, meaning that the pullback of $\mathcal L$ along the right translation $L.\mathrm{mulRight}\, t\, x : A \times_{\operatorname{Spec} R} T \to A$ and the pullback of $\mathcal L$ along the first projection are locally isomorphic over $T$: each point of $T$ has an open neighbourhood $U$ over whose preimage the two pullbacks become isomorphic. Let $y_1, y_2 : \operatorname{Spec} R \to K$ be two sections of $\iota$ followed by $f$. Then there is an isomorphism $\tau : K \cong K$ with $\tau$ followed by $\iota \circ f$ equal to $\iota \circ f$, that is an automorphism of $K$ over $\operatorname{Spec} R$, such that $y_1$ followed by $\tau$ is $y_2$.
--
--   This is the statement that the group of $R$-sections of the stabiliser subscheme $K(\mathcal L)$ of a line bundle under a relative group law acts on that subscheme by translations, so that any one section can be carried to any other by an automorphism over the base. It is used in the subsequent counting argument bounding the number of such sections, [`GoodReductionJacobian.RelativeGroupLaw.natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer`](thm.html#GoodReductionJacobian.RelativeGroupLaw.natCard_setOf_exists_comp_eq_dvd_finrank_of_forall_iff_isInStabilizer), where the transitive translation action converts a cardinality statement into a divisibility.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u v

theorem GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer
    {R : Type u} [CommRing R] {A K : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (𝓛 : A.Modules) (ι : K ⟶ A) [Mono ι]
    (hK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      (∃ κ : T ⟶ K, κ ≫ ι = x.1) ↔ L.IsInStabilizer 𝓛 t x)
    (y₁ y₂ : Spec (CommRingCat.of R) ⟶ K) (h₁ : y₁ ≫ ι ≫ f = 𝟙 _) (h₂ : y₂ ≫ ι ≫ f = 𝟙 _) :
    ∃ τ : K ≅ K, τ.hom ≫ ι ≫ f = ι ≫ f ∧ y₁ ≫ τ.hom = y₂ := by sorry
