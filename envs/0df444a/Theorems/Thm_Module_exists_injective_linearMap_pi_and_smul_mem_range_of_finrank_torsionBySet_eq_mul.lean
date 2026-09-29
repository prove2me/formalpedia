-- Prove2me | Theorems.Thm_Module_exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul
-- name    : Module.exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/5c5dd236-84f8-5685-98a6-20e03c8dde46
-- title:
--   Freeness up to finite index from constant eigen-lattice rank
-- statement:
--   Let $\mathcal{O}$ be a principal ideal domain, $T$ a commutative $\mathcal{O}$-algebra that is finite as an $\mathcal{O}$-module, and $M$ an abelian group carrying compatible $T$- and $\mathcal{O}$-module structures (the $\mathcal{O}$-action factoring through $T$ by a scalar-tower hypothesis) which is finite as an $\mathcal{O}$-module and torsion-free over $\mathcal{O}$. Let $\iota$ be a finite index type and, for each $i$, let $A_i$ be an integral domain which is an $\mathcal{O}$-algebra torsion-free as an $\mathcal{O}$-module, and $\chi_i \colon T \to A_i$ an $\mathcal{O}$-algebra homomorphism. Assume the $\chi_i$ are jointly injective, $\bigsqcap_i \ker \chi_i = 0$; that there is $a \in \mathcal{O}$, $a \neq 0$, such that for every tuple $(y_i)_i \in \prod_i A_i$ there is $x \in T$ with $\chi_i(x) = a \cdot y_i$ for all $i$; and that for some $d \in \mathbb{N}$ and all $i$ the $\mathcal{O}$-rank of the submodule of $M$ annihilated by every element of $\ker \chi_i$ equals $d$ times the $\mathcal{O}$-rank of $T/\ker \chi_i$. Then there exist a $T$-linear map $f \colon T^{d} \to M$ (source indexed by `Fin d`) and a non-zero $c \in \mathcal{O}$ such that $f$ is injective and $c \cdot m$ lies in the image of $f$ for every $m \in M$.
--
--   This is the lattice-theoretic criterion turning a uniform multiplicity count at each of finitely many jointly injective, finite-index characters of a finite $\mathcal{O}$-algebra $T$ into the existence of a free $T$-lattice $T^d \subseteq M$ of finite index, equivalently freeness of rank $d$ after inverting a non-zero element of $\mathcal{O}$. It is applied to localised Hecke modules, where the characters are the points of the Hecke algebra attached to newforms, in the corner-realisation step [`CuspForm.heckeLocal.exists_injective_linearMap_pi_and_smul_mem_range_of_isCornerRealization_of_not_cube_dvd`](thm.html#CuspForm.heckeLocal.exists_injective_linearMap_pi_and_smul_mem_range_of_isCornerRealization_of_not_cube_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul.lean

import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.exists_injective_linearMap_pi_and_smul_mem_range_of_finrank_torsionBySet_eq_mul
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    {T : Type*} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    {M : Type*} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.IsTorsionFree 𝒪 M]
    {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)] [∀ i, Algebra 𝒪 (A i)]
    [∀ i, Module.IsTorsionFree 𝒪 (A i)]
    (χ : ∀ i, T →ₐ[𝒪] A i) (hker : ⨅ i, RingHom.ker (χ i) = ⊥)
    (a : 𝒪) (ha : a ≠ 0) (hsurj : ∀ y : ∀ i, A i, ∃ x : T, ∀ i, χ i x = a • y i)
    (d : ℕ)
    (hrank : ∀ i, Module.finrank 𝒪 ↥(Submodule.torsionBySet T M ↑(RingHom.ker (χ i))) =
      d * Module.finrank 𝒪 (T ⧸ RingHom.ker (χ i))) :
    ∃ (f : (Fin d → T) →ₗ[T] M) (c : 𝒪), c ≠ 0 ∧ Function.Injective f ∧
      ∀ m : M, c • m ∈ LinearMap.range f := by sorry
