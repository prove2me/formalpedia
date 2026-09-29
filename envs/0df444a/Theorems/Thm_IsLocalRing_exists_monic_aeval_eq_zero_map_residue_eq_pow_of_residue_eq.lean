-- Prove2me | Theorems.Thm_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq
-- name    : IsLocalRing.exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/612f274e-daf6-5bb2-80e9-47f7bf63c10d
-- title:
--   Residual constancy passes to any 𝒪-algebra point
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring and $A$ a commutative local $\mathcal{O}$-algebra which is finite and free as an $\mathcal{O}$-module, with $\mathcal{O}\to A$ a local homomorphism, so that there is an induced map $\mathrm{ResidueField}(\mathcal{O})\to\mathrm{ResidueField}(A)$ on residue fields. Let $F$ be any commutative $\mathcal{O}$-algebra (not assumed local), $\varphi\colon A\to F$ an $\mathcal{O}$-algebra homomorphism, $x\in A$, and $c$ an element of the residue field of $\mathcal{O}$. Assume the residue of $x$ in the residue field of $A$ is the image of $c$ under the induced residue-field map. Then there exists a monic polynomial $R\in\mathcal{O}[X]$ such that $R(\varphi(x))=0$ in $F$ and such that the reduction of $R$ modulo the maximal ideal of $\mathcal{O}$ equals $(X-c)^{\deg R}$ in $\mathrm{ResidueField}(\mathcal{O})[X]$, the exponent being the degree of $R$ itself. Thus the congruence "$x\equiv c$" is transported to $\varphi(x)$ in the polynomial form that makes sense in any $\mathcal{O}$-algebra, where no residue map need be available.
--
--   This is the standard device for carrying residual information about an eigenvalue from a finite free local algebra into an arbitrary $\mathcal{O}$-algebra, for instance into an algebraic closure of the fraction field, where the residue map is unavailable. It is used in the study of localised Hecke algebras: in the production of an eigenform with prescribed residual unit root at an ordinary prime, in the computation of newform multiplicities as dimensions of eigenspaces for corner realisations, and in the count of residual root multiplicities in the non-ordinary case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq.lean

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Polynomial.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem IsLocalRing.exists_monic_aeval_eq_zero_map_residue_eq_pow_of_residue_eq
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] [Module.Free 𝒪 A]
    [IsLocalHom (algebraMap 𝒪 A)]
    {F : Type} [CommRing F] [Algebra 𝒪 F]
    (φ : A →ₐ[𝒪] F) (x : A) (c : IsLocalRing.ResidueField 𝒪)
    (hx : IsLocalRing.residue A x = IsLocalRing.ResidueField.map (algebraMap 𝒪 A) c) :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval (φ x) R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C c) ^ R.natDegree) := by sorry
