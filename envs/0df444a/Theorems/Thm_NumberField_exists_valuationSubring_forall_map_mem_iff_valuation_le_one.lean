-- Prove2me | Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
-- name    : NumberField.exists_valuationSubring_forall_map_mem_iff_valuation_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/d4e02e26-9940-5bbe-86a3-d9c18554ce9c
-- title:
--   Finite primes of a number field extend to places of ℚ̄
-- statement:
--   Let $F$ be a number field (a field of characteristic zero, finite-dimensional over $\mathbb{Q}$), let $\sigma : F \to \overline{\mathbb{Q}}$ be a ring homomorphism into a fixed algebraic closure of $\mathbb{Q}$, and let $v$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_F$, that is, a nonzero prime ideal of $\mathcal{O}_F$. The assertion is that there exists a valuation subring $B$ of $\overline{\mathbb{Q}}$ such that for every $x \in F$ one has $\sigma x \in B$ if and only if $v.\mathrm{valuation}\,F\,x \le 1$, where $v.\mathrm{valuation}$ denotes the $v$-adic valuation on $F$ attached to the height-one prime $v$. In other words, the preimage $\sigma^{-1}(B)$ is exactly the valuation ring of $v$ inside $F$; no compatibility hypothesis on $\sigma$ beyond its being a ring homomorphism is required, and the valuation subring $B$ is not claimed to be unique.
--
--   This is the statement that every finite place of a number field extends to a place of $\overline{\mathbb{Q}}$ along an arbitrary embedding, a special case of Chevalley's extension theorem for valuations. It is used in the arithmetic of levels, in particular to produce primes above a given prime in towers of fields inside $\overline{\mathbb{Q}}$, and it specialises to the corresponding statement for the inclusion of an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.exists_valuationSubring_forall_map_mem_iff_valuation_le_one
    (F : Type) [Field F] [NumberField F] (σ : F →+* AlgebraicClosure ℚ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ B : ValuationSubring (AlgebraicClosure ℚ), ∀ x : F, σ x ∈ B ↔ v.valuation F x ≤ 1 := by sorry
