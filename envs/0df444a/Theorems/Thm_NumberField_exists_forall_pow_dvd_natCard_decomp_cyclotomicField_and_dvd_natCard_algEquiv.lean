-- Prove2me | Theorems.Thm_NumberField_exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv
-- name    : NumberField.exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/a217450a-31a4-5c11-8864-d25c1ed27938
-- title:
--   p^N divides degree and local degrees of deep cyclotomic layers
-- statement:
--   Let $E$ be a number field, let $T$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_E$, let $p$ be a prime and let $N$ be a natural number. The assertion is that there exists $k_0 \in \mathbb{N}$ such that for every $k \ge k_0$, with $C_k :=$ `CyclotomicField (p ^ k) E` the $p^k$-th cyclotomic extension of $E$, two divisibilities hold. First, $p^N$ divides the cardinality of the group $C_k \simeq_{\mathrm{alg}[E]} C_k$ of $E$-algebra automorphisms of $C_k$ (as a `Nat.card`). Second, for every $v \in T$ and every height-one prime $w$ of $\mathcal{O}_{C_k}$ whose contraction `w.under (𝓞 E)` to $\mathcal{O}_E$ equals $v$, the number $p^N$ divides the cardinality of [`NumberField.PlaceDecomp.decomp E C_k w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup attached to $w$: the subgroup of those $E$-automorphisms of $C_k$ that preserve the valuation subring of the $w$-adic valuation of $C_k$. Equivalently, by [`NumberField.PlaceTransport.stabilizer_eq_decomp`](thm.html#NumberField.PlaceTransport.stabilizer_eq_decomp), this is the stabiliser of $w$ under the action of $C_k \simeq_{\mathrm{alg}[E]} C_k$ on height-one primes.
--
--   This is the arithmetic core of Artin's lemma on auxiliary cyclotomic extensions: sufficiently deep $p$-power cyclotomic layers over a number field have both global degree and local degrees (orders of decomposition groups) at a prescribed finite set of primes divisible by any prescribed power of $p$. It is used by [`NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp`](thm.html#NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp), which extracts from such a layer a cyclic quotient with the same divisibility properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
open NumberField IsDedekindDomain

theorem NumberField.exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv
    (E : Type) [Field E] [NumberField E] (T : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) [Fact p.Prime] (N : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      p ^ N ∣ Nat.card (CyclotomicField (p ^ k) E ≃ₐ[E] CyclotomicField (p ^ k) E) ∧
      ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 (CyclotomicField (p ^ k) E)), w.under (𝓞 E) = v →
        p ^ N ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E (CyclotomicField (p ^ k) E) w) := by sorry
