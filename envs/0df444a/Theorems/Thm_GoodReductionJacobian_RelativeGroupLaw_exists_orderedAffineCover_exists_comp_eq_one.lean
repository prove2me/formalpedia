-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_exists_comp_eq_one
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_orderedAffineCover_exists_comp_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/d2fa9368-853d-53ed-8428-0b2d02063546
-- title:
--   Unit section of a relative group law lies in one affine chart
-- statement:
--   Let $B$ be a commutative local ring and let $f : A \to \operatorname{Spec} B$ be a morphism of schemes (in universe $0$). Suppose given a relative group law $L$ for $f$, i.e. for every scheme $T$ and every $t : T \to \operatorname{Spec} B$ a multiplication, a unit element $L.\mathrm{one}(t)$ and an inversion on the set $\{\varphi : T \to A \mid \varphi \circ f^{\vee} \text{ over } t\}$ of morphisms $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, subject to associativity, the two unit laws, left inverses, and naturality of the multiplication under base change along $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$; suppose also $f$ satisfies the property bundle `AbelianSchemePropertyBundle`, namely $f$ is smooth, $f$ is proper, every fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} B$ is connected, and $f$ admits some relative group law. The conclusion asserts the existence of an ordered affine cover $\mathcal{U}$ of $A$ — a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq A$, each affine, with $\bigsqcup_i U_i = \top$ — an index $i_0$, and a morphism $e_0 : \operatorname{Spec} B \to U_{i_0}$ such that $e_0$ followed by the open immersion $U_{i_0} \hookrightarrow A$ equals the underlying morphism of the unit section $L.\mathrm{one}(\mathrm{id}_{\operatorname{Spec} B})$. Of the four parts of the bundle, the proof uses only properness of $f$, and of $L$ only its unit over the identity.
--
--   This is the geometric preliminary for working with the unit section of an abelian scheme over a local base in Čech terms: the section is confined to a single affine chart of a finite ordered affine cover, so that local computations around the identity can be carried out in one affine coordinate ring. It is used in the construction of formal coordinates along the unit section in [`GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_orderedAffineCover_exists_comp_eq_one.lean

import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_orderedAffineCover_exists_comp_eq_one
    {B : Type} [CommRing B] [IsLocalRing B] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of B))
    (L : RelativeGroupLaw B f) (hA : AbelianSchemePropertyBundle B f) :
    ∃ (𝒰 : A.OrderedAffineCover) (i₀ : 𝒰.ι) (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)),
      e₀ ≫ (𝒰.U i₀).ι = (L.one (𝟙 _)).1 := by sorry
