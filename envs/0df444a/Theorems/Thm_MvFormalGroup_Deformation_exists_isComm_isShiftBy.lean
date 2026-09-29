-- Prove2me | Theorems.Thm_MvFormalGroup_Deformation_exists_isComm_isShiftBy
-- name    : MvFormalGroup.Deformation.exists_isComm_isShiftBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/5d05f371-7816-561a-9ec3-749d564a75b9
-- title:
--   First-order classes shift commutative lifts of formal group laws
-- statement:
--   Let $B$ be a local commutative ring, $B_1$ a commutative $B$-algebra whose structure map has kernel contained in the maximal ideal of $B$. Let $V$ be an abelian group carrying a module structure over the residue field of $B$, finite as such, together with a compatible $B$-module structure (a scalar-tower assumption), and let $\iota : V \to B$ be an injective $B$-linear map whose range, viewed as a $B$-submodule of $B$, is exactly the kernel of $B \to B_1$. Let $F$ be a $d$-dimensional formal group law over $B$ (a $d$-tuple of power series in $2d$ variables with vanishing constant terms, linear terms $X_i$ and $Y_i$, and satisfying associativity) which is commutative, and let $w$ be a residue-field-linear map from the dual of $V$ to the first-order deformation space of $F \bmod \mathfrak m_B$, i.e. the quotient of the span of $\varepsilon$-parts of commutative deformations over the dual numbers by the span of those $\varepsilon$-parts that become $0$ after an isomorphism of deformations. Finally, let $G$ be a deformation of $F \otimes_B B_1$ to $B$, that is a formal group law $G.F$ over $B$ reducing to $F \otimes_B B_1$, with $G.F$ commutative. Then there exists a deformation $G'$ of $F \otimes_B B_1$ to $B$ with $G'.F$ commutative such that `Deformation.IsShiftBy V ι F w G G'` holds: for some $n$ there are $v_i \in V$, first-order cocycles $z_i$ for $F \bmod \mathfrak m_B$ and coefficientwise lifts $\tilde z_i$ of the $z_i$ to power series over $B$ with $w(\xi) = \sum_i \xi(v_i)\,[z_i]$ for every functional $\xi$ on $V$, and $G'.F$ given componentwise by $G.F + \sum_i \iota(v_i)\cdot \tilde z_i$.
--
--   This is the surjectivity (everywhere-definedness) half of the statement that the tangent space to the deformation functor acts on the set of lifts of a formal group law along a small surjection $B \to B_1$: every first-order class $w$ shifts every given commutative lift to another one. It is used in the construction of formal coordinates on Jacobians with good reduction, in [`GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_Deformation_exists_isComm_isShiftBy.lean

import Mathlib
import Definitions.Def_MvFormalGroup_IsShiftBy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing MvFormalGroup

theorem MvFormalGroup.Deformation.exists_isComm_isShiftBy
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]
    (w : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (G : Deformation (F.map (algebraMap B B₁)) B) [G.F.IsComm] :
    ∃ G' : Deformation (F.map (algebraMap B B₁)) B, G'.F.IsComm ∧ Deformation.IsShiftBy V ι F w G G' := by sorry
