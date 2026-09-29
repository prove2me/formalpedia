-- Prove2me | Theorems.Thm_MvFormalGroup_Deformation_isShiftBy_of_isIso_of_isIso
-- name    : MvFormalGroup.Deformation.isShiftBy_of_isIso_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/d1a27040-8b46-5123-abdc-62e7cdd784b7
-- title:
--   Shift relation invariant under strict isomorphism of deformations
-- statement:
--   Let $B$ be a commutative local ring and $B_1$ a commutative $B$-algebra whose structure map has kernel contained in the maximal ideal of $B$. Let $V$ be an abelian group carrying a module structure over the residue field of $B$, finite as a module over it, together with a $B$-module structure compatible with the residue-field one via the scalar tower, and let $\iota : V \to B$ be an injective $B$-linear map whose range, viewed as a $B$-submodule, is exactly the kernel of $B \to B_1$. Let $F$ be a commutative $d$-dimensional formal group law over $B$ and let $w$ be a residue-field-linear map from the dual of $V$ to the first-order deformation space of the reduction $F \bmod \mathfrak m$. Let $G, G', G_2, G_2'$ be deformations of $F \otimes_B B_1$ over $B$, i.e. formal group laws over $B$ whose images under $B \to B_1$ coincide with that of $F$, each with commutative underlying law. Assume `Deformation.IsShiftBy V ι F w G G'`, i.e. there are $n$, vectors $v_i \in V$, first-order cocycles $z_i$ for $F \bmod \mathfrak m$ with chosen lifts $z^{\mathrm l}_i$ over $B$ reducing to $z_i$ coefficientwise, such that $w(\xi) = \sum_i \xi(v_i)\,[z_i]$ for every functional $\xi$ on $V$ and $G'.F = G.F + \sum_i \iota(v_i) \cdot z^{\mathrm l}_i$ componentwise. Assume further that $G$ and $G_2$, and $G'$ and $G_2'$, are isomorphic as deformations, in the sense that there is a homomorphism of formal group laws with a two-sided inverse whose component power series reduce to the coordinates $X_i$ over $B_1$. Then `Deformation.IsShiftBy V ι F w G₂ G₂'` holds, with the same $w$.
--
--   This is the well-definedness of the shift operation on deformations: shifting by a first-order class is compatible with passage to strict isomorphism classes on both sides, so that, combined with the additivity and neutrality statement [`MvFormalGroup.Deformation.isShiftBy_zero_and_isShiftBy_add`](thm.html#MvFormalGroup.Deformation.isShiftBy_zero_and_isShiftBy_add), the first-order deformation space acts on isomorphism classes of deformations. It is used in the analysis of bare deformations of Jacobians with good reduction, in particular in the construction of formal coordinates and in the comparison of shifts with regluing data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_Deformation_isShiftBy_of_isIso_of_isIso.lean

import Mathlib
import Definitions.Def_MvFormalGroup_IsShiftBy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing MvFormalGroup

theorem MvFormalGroup.Deformation.isShiftBy_of_isIso_of_isIso
    {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))
    {d : ℕ} (F : MvFormalGroup d B) [F.IsComm]
    (w : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (G G' G₂ G₂' : Deformation (F.map (algebraMap B B₁)) B) [G.F.IsComm] [G'.F.IsComm] [G₂.F.IsComm] [G₂'.F.IsComm]
    (h : Deformation.IsShiftBy V ι F w G G') (h₂ : G.IsIso G₂) (h₂' : G'.IsIso G₂') :
    Deformation.IsShiftBy V ι F w G₂ G₂' := by sorry
