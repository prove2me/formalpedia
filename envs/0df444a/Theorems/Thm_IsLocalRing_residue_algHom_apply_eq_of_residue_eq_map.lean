-- Prove2me | Theorems.Thm_IsLocalRing_residue_algHom_apply_eq_of_residue_eq_map
-- name    : IsLocalRing.residue_algHom_apply_eq_of_residue_eq_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/f684bbb1-b1ef-5336-9754-4210382f8fce
-- title:
--   𝒪-algebra points of local algebras preserve residues
-- statement:
--   Let $\mathcal O$ be a commutative local ring and $L$ a commutative local ring equipped with an $\mathcal O$-algebra structure whose structure map $\mathcal O \to L$ is local, i.e. pulls back non-units to non-units (so that it induces a map $\mathrm{ResidueField}(\mathcal O) \to \mathrm{ResidueField}(L)$, written `IsLocalRing.ResidueField.map`). Let $\pi_T \colon L \to \mathcal O$ be a homomorphism of $\mathcal O$-algebras, let $z \in L$, and let $x$ be an element of the residue field of $\mathcal O$. Assume that the residue class of $z$ in the residue field of $L$ equals the image of $x$ under the induced map of residue fields. The conclusion is that the residue class of $\pi_T(z)$ in the residue field of $\mathcal O$ is equal to $x$. In other words, the reduction of any $\mathcal O$-algebra retraction $\pi_T$ of $L$ is a retraction of $\mathrm{ResidueField}(\mathcal O) \to \mathrm{ResidueField}(L)$ at the level of elements: reading off $\pi_T(z)$ modulo the maximal ideal of $\mathcal O$ recovers the residue of $z$ whenever that residue comes from $\mathcal O$.
--
--   This is the elementary statement that an $\mathcal O$-valued point of a local $\mathcal O$-algebra is compatible with passage to residue fields. In the formalisation it is applied to localised Hecke algebras, where it shows that the $\mathcal O$-valued points attached to newform eigensystems reduce to the prescribed residual eigensystem; it is used in the construction and comparison of corner data and eigenspace dimension bounds at level $N$ and $Np$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_residue_algHom_apply_eq_of_residue_eq_map.lean

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Algebra.Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.residue_algHom_apply_eq_of_residue_eq_map
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {L : Type} [CommRing L] [IsLocalRing L] [Algebra 𝒪 L] [IsLocalHom (algebraMap 𝒪 L)]
    (πT : L →ₐ[𝒪] 𝒪) (z : L) (x : IsLocalRing.ResidueField 𝒪)
    (hz : IsLocalRing.residue L z = IsLocalRing.ResidueField.map (algebraMap 𝒪 L) x) :
    IsLocalRing.residue 𝒪 (πT z) = x := by sorry
