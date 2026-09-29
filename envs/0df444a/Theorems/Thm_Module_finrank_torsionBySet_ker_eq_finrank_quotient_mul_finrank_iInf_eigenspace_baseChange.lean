-- Prove2me | Theorems.Thm_Module_finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange
-- name    : Module.finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/d0c2b990-4604-5fad-9efc-bbe0628ffa51
-- title:
--   Rank of the kerχ-torsion submodule after base change
-- statement:
--   Let $\mathcal{O}$ be a principal ideal domain, let $T$ be a commutative $\mathcal{O}$-algebra that is finite as an $\mathcal{O}$-module, and let $M$ be an additive group carrying compatible $T$- and $\mathcal{O}$-module structures (the $\mathcal{O}$-action factoring through $T$ via a scalar tower) which is finite and torsion-free as an $\mathcal{O}$-module. Let $A$ be a commutative domain which is an $\mathcal{O}$-algebra, finite and torsion-free as an $\mathcal{O}$-module, and let $\chi : T \to A$ be an $\mathcal{O}$-algebra homomorphism. The assertion is an equality of $\mathcal{O}$-ranks and $A$-ranks: the $\mathcal{O}$-rank of the submodule of $M$ annihilated by every element of the ideal $\ker\chi$, i.e. $M[\ker\chi] = \{m \in M : t\,m = 0 \text{ for all } t \in \ker\chi\}$, equals the $\mathcal{O}$-rank of the quotient ring $T/\ker\chi$ multiplied by the $A$-rank of the intersection, over all $t \in T$, of the eigenspaces for the eigenvalue $\chi(t)$ of the $A$-linear endomorphism of $A \otimes_{\mathcal{O}} M$ obtained by base change along $\mathcal{O} \to A$ from the $\mathcal{O}$-linear map $m \mapsto t\,m$ on $M$.
--
--   This is the integral form of the comparison between the multiplicity of a system of eigenvalues computed in a lattice and the same multiplicity computed after enlarging the coefficient ring: the rank of the $\ker\chi$-torsion lattice over the order $T/\ker\chi$ is the rank of the $\chi$-eigenspace of the base change, independently of how large $A$ is. It is applied to localised Hecke modules attached to cusp forms, where the multiplicity of a newform is naturally read off after extending scalars to a ring containing its eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange.lean

import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Module.finrank_torsionBySet_ker_eq_finrank_quotient_mul_finrank_iInf_eigenspace_baseChange
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {T : Type*} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    [Module.IsTorsionFree 𝒪 A]
    (χ : T →ₐ[𝒪] A) :
    Module.finrank 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker χ)) =
      Module.finrank 𝒪 (T ⧸ RingHom.ker χ) *
        Module.finrank A ↥(⨅ t : T, Module.End.eigenspace
          (((LinearMap.lsmul T M t).restrictScalars 𝒪).baseChange A) (χ t)) := by sorry
