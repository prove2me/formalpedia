-- Prove2me | Theorems.Thm_MvFormalGroup_Deformation_isIso_of_isShiftBy_of_isShiftBy
-- name    : MvFormalGroup.Deformation.isIso_of_isShiftBy_of_isShiftBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/946d00d0-254b-5c94-a1c3-d5d81f801e4b
-- title:
--   Two shifts of a deformation by the same class are isomorphic
-- statement:
--   Let $B$ be a commutative local ring and $B_1$ a commutative $B$-algebra such that the kernel $J$ of $B \to B_1$ is contained in the maximal ideal of $B$. Let $V$ be a finite-dimensional module over the residue field of $B$, also a $B$-module compatibly through the residue map, and let $\iota : V \to B$ be an injective $B$-linear map whose range is exactly $J$ (as a $B$-submodule). Let $F$ be a commutative $d$-dimensional formal group law over $B$: a $d$-tuple of power series in two families of $d$ variables with vanishing constant terms, the expected linear coefficients, and the associativity and symmetry identities. Let $w$ be a residue-field-linear map from the dual of $V$ to the first-order deformation space of $F$ reduced modulo the maximal ideal, i.e. the quotient of the first-order cocycles by the first-order coboundaries. Let $G, G', G''$ be deformations of $F \otimes_B B_1$ over $B$ — formal group laws over $B$ with commutative underlying laws whose base change along $B \to B_1$ is $F \otimes_B B_1$. Assume both $G'$ and $G''$ are obtained from $G$ by a shift by $w$: for each, there are finitely many $v_i \in V$, cocycles $z_i$ over the residue field with lifts $z_{i}^{\sim}$ over $B$ reducing to them, such that $w\xi = \sum_i \xi(v_i)\,[z_i]$ for every functional $\xi$, and the group law of the shifted deformation is that of $G$ plus $\sum_i \iota(v_i)\, z_i^{\sim}$ coefficientwise. Then $G'$ and $G''$ are isomorphic as deformations: there is a homomorphism of formal group laws $G'.F \to G''.F$ over $B$ with a two-sided inverse whose power series reduce to the coordinate variables $X_i$ over $B_1$.
--
--   This is the well-definedness of the shift action of first-order deformation classes on strict isomorphism classes of deformations: shifting a fixed lift by a fixed class determines the lift up to strict isomorphism over $B_1$. It is used in the construction of formal coordinates on Jacobians with good reduction, where lifts are built by successive small extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_Deformation_isIso_of_isShiftBy_of_isShiftBy.lean

import Mathlib
import Definitions.Def_MvFormalGroup_IsShiftBy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing MvFormalGroup

theorem MvFormalGroup.Deformation.isIso_of_isShiftBy_of_isShiftBy
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]
    (w : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (G G' G'' : Deformation (F.map (algebraMap B B₁)) B) [G.F.IsComm] [G'.F.IsComm] [G''.F.IsComm]
    (h' : Deformation.IsShiftBy V ι F w G G') (h'' : Deformation.IsShiftBy V ι F w G G'') :
    G'.IsIso G'' := by sorry
