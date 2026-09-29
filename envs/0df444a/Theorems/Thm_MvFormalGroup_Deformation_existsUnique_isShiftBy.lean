-- Prove2me | Theorems.Thm_MvFormalGroup_Deformation_existsUnique_isShiftBy
-- name    : MvFormalGroup.Deformation.existsUnique_isShiftBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/4a90a938-9492-5ff3-9e03-7e2ce07bd7e8
-- title:
--   Two lifts differ by a unique first-order class
-- statement:
--   Let $B$ be a commutative local ring with residue field $k =$ `ResidueField B`, and let $B_1$ be a commutative $B$-algebra whose structure map has kernel $J = \ker(B \to B_1)$ contained in the maximal ideal of $B$. Let $V$ be a finite-dimensional $k$-vector space, also regarded as a $B$-module via the scalar tower $B \to k$, and let $\iota : V \to B$ be an injective $B$-linear map whose image, as a $B$-submodule of $B$, is exactly $J$. Let $d \in \mathbb{N}$ and let $F$ be a $d$-dimensional formal group law over $B$ (a $d$-tuple of power series in the $2d$ variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$, with vanishing constant terms, linear parts $X_i + Y_i$, and associativity), assumed commutative. Let $G$ and $G'$ be two deformations of $F \otimes_B B_1$ to $B$, that is, commutative $d$-dimensional formal group laws $G.F$, $G'.F$ over $B$ whose base changes along $B \to B_1$ both equal $F \otimes_B B_1$. Then there is exactly one $k$-linear map $w$ from the dual space $V^\vee$ to the first-order deformation space of $F \otimes_B k$ (the quotient of the module `firstOrderCocycles` of first-order cocycles of $F \otimes_B k$ by the first-order coboundaries lying in it) satisfying `Deformation.IsShiftBy V ι F w G G'`: there are $n \in \mathbb{N}$, vectors $v_1,\dots,v_n \in V$, cocycles $z_1,\dots,z_n$ for $F \otimes_B k$, and $d$-tuples $\tilde z_i$ of power series over $B$ reducing coefficientwise modulo the maximal ideal to $z_i$, such that $w(\xi) = \sum_i \xi(v_i)\,[z_i]$ for every $\xi \in V^\vee$ and $G'.F$ has $l$-th component $G.F_l + \sum_i \iota(v_i)\,\tilde z_{i,l}$ for each $l$.
--
--   This is the statement that the group of first-order deformations of the reduction $F \otimes_B k$, twisted by the ideal $J$, acts simply transitively on the lifts of $F \otimes_B B_1$ to $B$ along the small surjection $B \to B_1$: any two such lifts differ by a shift, and the shifting class is unique. It is used in the study of formal group laws attached to Jacobians with good reduction, namely in the construction of formal coordinates lifting a given system of coordinates and in the construction of the linear map on point derivations attached to a pair of deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_Deformation_existsUnique_isShiftBy.lean

import Mathlib
import Definitions.Def_MvFormalGroup_IsShiftBy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing MvFormalGroup

theorem MvFormalGroup.Deformation.existsUnique_isShiftBy
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]
    (G G' : Deformation (F.map (algebraMap B B₁)) B) [G.F.IsComm] [G'.F.IsComm] :
    ∃! w : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)),
      Deformation.IsShiftBy V ι F w G G' := by sorry
