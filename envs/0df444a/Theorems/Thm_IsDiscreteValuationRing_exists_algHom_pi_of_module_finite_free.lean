-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_algHom_pi_of_module_finite_free
-- name    : IsDiscreteValuationRing.exists_algHom_pi_of_module_finite_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/736b2c9d-5c23-537c-a7dd-dab917a25c5e
-- title:
--   Reduced finite free 𝒪-algebras embed into products of complete DVRs
-- statement:
--   Let $\mathcal{O}$ be a commutative ring which is a domain and a discrete valuation ring, complete with respect to the adic filtration by its maximal ideal, with finite residue field and of characteristic $0$. Let $T$ be a commutative ring which is reduced, equipped with an $\mathcal{O}$-algebra structure making it finite and free as an $\mathcal{O}$-module. The assertion is that there exist a natural number $n$ and a family of rings $R_j$ indexed by $j \in \mathrm{Fin}\,n$, each carrying a commutative ring structure under which it is a domain and a discrete valuation ring, complete with respect to the adic filtration by its maximal ideal, with finite residue field and of characteristic $0$, and each carrying an $\mathcal{O}$-algebra structure whose structure map $\mathcal{O} \to R_j$ is a local homomorphism, together with a homomorphism of $\mathcal{O}$-algebras $\iota : T \to \prod_{j} R_j$ which is injective. Note that the $R_j$ are not asserted to be finite as $\mathcal{O}$-modules, nor is any compatibility of $\iota$ with the minimal primes of $T$ recorded; only injectivity and the listed properties of the factors are claimed.
--
--   This is the standard first step in attaching Galois representations to a reduced Hecke algebra: the algebra is embedded into the product of the coefficient rings of the eigenforms occurring in it, each of which is a complete discrete valuation ring of characteristic $0$ with finite residue field, local over $\mathcal{O}$. It is used in the verification that the Hecke operator $T_\ell$ acts with trace equal to the trace of Frobenius, via [`CuspForm.heckeLocal.exists_smul_eq_heckeT_and_apply_eq_trace_frobenius_of_not_dvd`](thm.html#CuspForm.heckeLocal.exists_smul_eq_heckeT_and_apply_eq_trace_frobenius_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_algHom_pi_of_module_finite_free.lean

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsDiscreteValuationRing.exists_algHom_pi_of_module_finite_free
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (T : Type) [CommRing T] [IsReduced T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T] :
    ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι := by sorry
