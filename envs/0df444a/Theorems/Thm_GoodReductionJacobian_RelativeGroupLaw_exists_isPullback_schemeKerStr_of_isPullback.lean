-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_schemeKerStr_of_isPullback
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isPullback_schemeKerStr_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/37abb00c-4af1-51d2-9074-fab15b6f433b
-- title:
--   Kernels of multiplication by n commute with base change
-- statement:
--   Let $\varphi : R \to R'$ be a homomorphism of commutative rings, let $f : A \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$ equipped with a relative group law $L$ and let $f' : A' \to \operatorname{Spec} R'$ be a scheme over $\operatorname{Spec} R'$ equipped with a relative group law $L'$; here a relative group law on $f$ consists of multiplication, unit and inverse operations on the sets $\{\,x : T \to A \mid x \circ f = t\,\}$ of points over each $t : T \to \operatorname{Spec} R$, satisfying associativity, two-sided unit, left inverse, and naturality of multiplication under precomposition with morphisms of bases. Let $g : A' \to A$ be a morphism such that the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}(\varphi)$ is cartesian, and assume that for every scheme $T$, every $t' : T \to \operatorname{Spec} R'$ and all points $P, Q$ of $A'$ over $t'$ one has $(L'.\mathrm{mul}\,t'\,P\,Q) \cdot g = L.\mathrm{mul}$ at $\operatorname{Spec}(\varphi) \circ t'$ applied to $g \circ P$ and $g \circ Q$, i.e. $g$ is multiplicative on points. Then for every $n \in \mathbb{N}$ there is a morphism $g_n$ from $L'.\mathrm{schemeKer}\,n$, the fibre product of the multiplication-by-$n$ morphism of $A'$ with the unit section of $A'$, to the corresponding $L.\mathrm{schemeKer}\,n$, such that the square formed by $g_n$, the two structure morphisms $L'.\mathrm{schemeKerStr}\,n$ and $L.\mathrm{schemeKerStr}\,n$ (the second projections to the bases) and $\operatorname{Spec}(\varphi)$ is cartesian, and such that $g_n$ followed by the first projection of the kernel of $A$ equals the first projection of the kernel of $A'$ followed by $g$.
--
--   This is the statement that the $n$-torsion subscheme of a scheme with a relative group law is compatible with base change: if $A'$ is a base change of $A$ along $R \to R'$ by a morphism multiplicative on points, then $A'[n] \cong A[n] \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ over $\operatorname{Spec} R'$, compatibly with the inclusions into $A'$ and $A$. It is used to transport torsion subgroup schemes and level structures of fake elliptic curves along base change, and is cited in the representability of extra level structures and in the clopen decomposition of level pieces in the deformation theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_schemeKerStr_of_isPullback.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isPullback_schemeKerStr_of_isPullback
    {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {A' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f')
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (n : ℕ) :
    ∃ gn : L'.schemeKer n ⟶ L.schemeKer n,
      IsPullback gn (L'.schemeKerStr n) (L.schemeKerStr n) (Spec.map (CommRingCat.ofHom φ)) ∧
      gn ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 =
        pullback.fst (L'.schemeNsmul n) (L'.one (𝟙 (Spec (CommRingCat.of R')))).1 ≫ g := by sorry
