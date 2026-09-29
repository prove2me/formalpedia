-- Prove2me | Theorems.Thm_Module_length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact
-- name    : Module.length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/7c9fcaaf-e7ca-51aa-aedb-023dccb5bab5
-- title:
--   Length duality for top cokernels of finite free complexes
-- statement:
--   Let $R$ be a commutative Noetherian local ring, $n$ a natural number, and $rs$ a list of elements of $R$ which is a regular sequence on $R$ (`RingTheory.Sequence.IsRegular`), of length $n+1$, and which generates the maximal ideal of $R$. Let $K : \mathbb{N} \to \mathrm{Type}$ be a family of $R$-modules, each finite and free, with $K i$ subsingleton for every $i > n+1$ (hypothesis `hbdd`), and let $\delta_i : K i \to K (i+1)$ be $R$-linear maps with $\delta_{i+1} \circ \delta_i = 0$ for all $i$, with $\delta_0$ injective, and with $\ker \delta_{i+1} \subseteq \operatorname{im} \delta_i$ for all $i < n$. Assume further that the cokernel $Q := K(n+1)/\operatorname{im} \delta_n$ is annihilated by some power $\mathfrak{m}^N$ of the maximal ideal. Then the $R$-module length of $Q$ equals the length of $\operatorname{Hom}_R(K 0, R)$ modulo the image of the transpose $\delta_0^{*}$ of $\delta_0$, i.e. of the cokernel of $\operatorname{Hom}_R(K 1, R) \to \operatorname{Hom}_R(K 0, R)$.
--
--   This is the length-preservation half of local duality for finite-length modules over a regular local ring, in the concrete form: if a finite free complex of length $n+1$ resolves its top cokernel $Q$ and $Q$ has finite length, then $\operatorname{length} Q = \operatorname{length} \operatorname{Ext}^{n+1}_R(Q,R)$, the latter computed as the top cohomology of the dual complex. It feeds the Euler-characteristic count [`Module.toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient`](thm.html#Module.toNat_length_ker_add_sum_neg_one_pow_toNat_length_eq_neg_one_pow_mul_toNat_length_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.length_quotient_range_eq_length_dual_quotient_of_isRegular_of_exact
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (n : ℕ) (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hlen : rs.length = n + 1)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
    (hbdd : ∀ i, n + 1 < i → Subsingleton (K i))
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (hex0 : ∀ z : K 0, δ 0 z = 0 → z = 0)
    (hex : ∀ i, i < n → ∀ z : K (i + 1), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i))
    (htors : ∃ N : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal R ^ N, ∀ q : K (n + 1) ⧸ LinearMap.range (δ n), a • q = 0) :
    Module.length R (K (n + 1) ⧸ LinearMap.range (δ n)) =
      Module.length R (Module.Dual R (K 0) ⧸ LinearMap.range (δ 0).dualMap) := by sorry
