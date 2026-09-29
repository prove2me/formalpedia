-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b46be7da-6714-5ede-a068-4b4da516a3d0
-- title:
--   Constant finite étale subgroup scheme over a discrete valuation ring
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the `IsDiscreteValuationRing` structure), let $f\colon A \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$, and let $L$ be a relative group law on $f$: for every scheme $T$ and every morphism $t\colon T \to \operatorname{Spec} R$ a multiplication `L.mul t`, a unit `L.one t` and an inversion on the set $\{\varphi\colon T \to A \mid \varphi \circ f = t\}$ of points of $A$ over $t$, satisfying associativity, both unit laws, left inverse, and compatibility of the multiplication with precomposition along any $\psi\colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Let $\mathrm{lev}\colon C \to A$ be a closed immersion such that $\mathrm{lev}$ followed by $f$ is finite and étale. Assume that for every $t\colon T \to \operatorname{Spec} R$ the unit `L.one t` factors through $\mathrm{lev}$, and that `L.mul t x y` factors through $\mathrm{lev}$ whenever $x$ and $y$ do. Then there is a finite group $G$ such that for every algebraically closed field $k$ and every ring homomorphism $sk\colon R \to k$ there is a bijection $e$ from $G$ onto the set of points of $A$ over $\operatorname{Spec}(sk)$ that factor through $\mathrm{lev}$, with $e(ab) = \mathrm{L.mul}(e\,a, e\,b)$ for all $a,b \in G$.
--
--   This is the constancy of a finite étale group scheme over the connected base $\operatorname{Spec} R$, phrased on geometric points: a single finite group describes the points factoring through $C$ over every geometric point of $\operatorname{Spec} R$, generic or special, with the multiplication induced by the relative group law. It is used in the study of fake elliptic curves to transport a description of the generic geometric fibre of the flat closure of a level structure to the special geometric fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {C : Scheme.{u}} (lev : C ⟶ A) [IsClosedImmersion lev] [IsFinite (lev ≫ f)] [Etale (lev ≫ f)]
    (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), ∃ z : T ⟶ C, z ≫ lev = (L.one t).1)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (∃ z : T ⟶ C, z ≫ lev = x.1) → (∃ z : T ⟶ C, z ≫ lev = y.1) → ∃ z : T ⟶ C, z ≫ lev = (L.mul t x y).1) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G),
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k),
        ∃ e : G ≃ {x : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f // ∃ z : _ ⟶ C, z ≫ lev = x.1},
          ∀ a b : G,
            ((e (a * b) : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f // ∃ z : _ ⟶ C, z ≫ lev = x.1}) :
                SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f) =
              L.mul (Spec.map (CommRingCat.ofHom sk)) (e a) (e b) := by sorry
