-- Prove2me | Theorems.Thm_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
-- name    : NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/14cecfbd-43a7-53ea-854e-00e9d5581568
-- title:
--   Valuation subrings of Ω pulled back along K → Ω give primes
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}_K$, let $\Omega$ be a field, let $\sigma \colon K \to \Omega$ be a ring homomorphism, and let $A$ be a valuation subring of $\Omega$, i.e. a subring such that every element of $\Omega$ lies in $A$ or has its inverse in $A$. Assume that $\sigma$ does not map all of $K$ into $A$: there is some $x \in K$ with $\sigma(x) \notin A$. Then there is exactly one element $v$ of the height-one spectrum of $\mathcal{O}_K$, that is, exactly one nonzero prime ideal $v$ of $\mathcal{O}_K$, such that for every $x \in K$ one has $\sigma(x) \in A$ if and only if $v(x) \le 1$, where $v(\cdot)$ denotes the $\mathbb{Z}_{m_0}$-valued $v$-adic valuation on $K$ attached to $v$ as a prime of the Dedekind domain $\mathcal{O}_K$. Equivalently, $\sigma^{-1}(A)$ is the valuation ring of a $v$-adic valuation on $K$, and $v$ is determined by this property. Uniqueness is asserted in the strong form $\exists!$.
--
--   This is the classification of the non-trivial valuation rings of a number field — Ostrowski's theorem in its non-archimedean form, or equivalently the description of the valuation overrings of a Dedekind domain as the localisations at nonzero primes — packaged as the dictionary sending a pair (embedding of $K$ into a field $\Omega$, valuation subring of $\Omega$ not containing the image) to a finite prime of $K$. It supports the arithmetic of $S$-units, $S$-class groups and their Galois cohomology used in the level-lowering input, where primes of $K$ must be recovered from places of a larger field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
    (K : Type) [Field K] [NumberField K] {Ω : Type} [Field Ω]
    (σ : K →+* Ω) (A : ValuationSubring Ω) (hA : ∃ x : K, σ x ∉ A) :
    ∃! v : HeightOneSpectrum (𝓞 K), ∀ x : K, σ x ∈ A ↔ v.valuation K x ≤ 1 := by sorry
