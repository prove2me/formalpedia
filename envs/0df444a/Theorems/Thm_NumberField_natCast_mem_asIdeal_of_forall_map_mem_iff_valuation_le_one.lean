-- Prove2me | Theorems.Thm_NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one
-- name    : NumberField.natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/714b895a-1f91-5a8f-addf-2be98a3687cd
-- title:
--   The prime attached to an embedding and place divides p
-- statement:
--   Let $K$ be a number field, $\Omega$ a field, $\sigma \colon K \to \Omega$ a ring homomorphism, $A \subseteq \Omega$ a valuation subring, and $v$ a point of the height-one spectrum of the ring of integers $\mathcal{O}_K$, that is, a nonzero prime ideal `v.asIdeal`. Assume that $A$ and $v$ correspond under $\sigma$ in the strong sense that for every $x \in K$ one has $\sigma(x) \in A$ if and only if the $v$-adic valuation of $x$ (the valuation on $K$ attached to $v$ by the Dedekind-domain machinery, extended from $\mathcal{O}_K$) satisfies $v(x) \le 1$. Let $p$ be a natural number and assume that the canonical valuation of $A$ on $\Omega$ takes a value $< 1$ at $\sigma(p)$, i.e. $\sigma(p)$ lies in the maximal ideal of $A$ rather than merely in $A$. The conclusion is that the image of $(p : \mathbb{Z})$ in $\mathcal{O}_K$ belongs to `v.asIdeal`, that is, $v$ divides $p$. Note that $p$ is not assumed prime, and $\sigma$ is not assumed injective.
--
--   This is the statement that, in the dictionary between valuation subrings of $\Omega$ pulled back along an embedding $\sigma$ and finite primes of $K$, the prime attached to a place lies over the residue characteristic of that place; taking $\Omega = \overline{\mathbb{Q}}$ and $A$ a place above a rational prime $p$, every prime produced by the dictionary divides $p$. It is used in the level-arithmetic part of the development, in the construction of an isomorphism for quotients by invariants of $S$-unit representations and in the criterion for a Kummer character to be level-constant in terms of divisibility of valuations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one
    (K : Type) [Field K] [NumberField K] {Ω : Type} [Field Ω]
    (σ : K →+* Ω) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ x : K, σ x ∈ A ↔ v.valuation K x ≤ 1)
    (p : ℕ) (hp : A.valuation (σ (p : K)) < 1) :
    ((p : ℤ) : 𝓞 K) ∈ v.asIdeal := by sorry
