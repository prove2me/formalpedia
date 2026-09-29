-- Prove2me | Theorems.Thm_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot
-- name    : IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/01fad9b2-b3f8-5263-b078-85fe33c18e49
-- title:
--   Points of a reduced finite local algebra into complete DVRs
-- statement:
--   Let $\mathcal{O}$ be a commutative ring which is a domain and a discrete valuation ring, complete for the adic topology of its maximal ideal, with finite residue field and of characteristic zero; let $P$ be a commutative local reduced $\mathcal{O}$-algebra which is finite and torsion-free as an $\mathcal{O}$-module. The assertion is that there exist a natural number $n$ and a family of types $A_i$, $i \in \mathrm{Fin}\ n$, each carrying a commutative ring structure making it a domain and a discrete valuation ring, complete for the adic topology of its maximal ideal, with finite residue field and of characteristic zero, each an $\mathcal{O}$-algebra that is finite as an $\mathcal{O}$-module and whose structure map $\mathcal{O} \to A_i$ is a local homomorphism, together with $\mathcal{O}$-algebra homomorphisms $\chi_i : P \to A_i$, such that each $\chi_i$ is a local homomorphism, the intersection $\bigcap_i \ker \chi_i$ is the zero ideal, and there is a nonzero $a \in \mathcal{O}$ with the property that for every element $y = (y_i)$ of $\prod_i A_i$ there is $x \in P$ with $\chi_i(x) = a \cdot y_i$ for all $i$; that is, $a \cdot \prod_i A_i$ lies in the image of $P$ under $(\chi_i)_i$.
--
--   This is the standard statement that a reduced module-finite torsion-free local algebra over a complete discrete valuation ring embeds, with cokernel killed by a single nonzero scalar, into a finite product of complete discrete valuation rings finite over the base, obtained from the normalisations of its quotients by the minimal primes. In the present development it is the source of the systems of characters of a Hecke algebra with values in rings of integers, and is invoked in the construction of Hecke eigenvectors in cohomology and in the associated comparisons of Frobenius characteristic polynomials and diamond operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_fin_points_dvr_iInf_ker_eq_bot.lean

import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct

theorem IsLocalRing.exists_fin_points_dvr_iInf_ker_eq_bot
    {𝒪 P : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    [CommRing P] [IsLocalRing P] [IsReduced P] [Algebra 𝒪 P] [Module.Finite 𝒪 P]
    [Module.IsTorsionFree 𝒪 P] :
    ∃ (n : ℕ) (A : Fin n → Type) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsDomain (A i))
      (_ : ∀ i, IsDiscreteValuationRing (A i))
      (_ : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (A i)) (A i))
      (_ : ∀ i, Finite (IsLocalRing.ResidueField (A i))) (_ : ∀ i, CharZero (A i))
      (_ : ∀ i, Algebra 𝒪 (A i)) (_ : ∀ i, Module.Finite 𝒪 (A i))
      (_ : ∀ i, IsLocalHom (algebraMap 𝒪 (A i)))
      (χ : ∀ i, P →ₐ[𝒪] A i),
      (∀ i, IsLocalHom (χ i).toRingHom) ∧ ⨅ i, RingHom.ker (χ i).toRingHom = ⊥ ∧
        ∃ a : 𝒪, a ≠ 0 ∧ ∀ y : ∀ i, A i, ∃ x : P, ∀ i, χ i x = a • y i := by sorry
