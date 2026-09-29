-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton
-- name    : IsDiscreteValuationRing.forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/fccf04d4-a2a7-5d6f-ad16-8f927ba95ca9
-- title:
--   Unique valuation ring over a totally ramified prime, and varpi = vπⁿ
-- statement:
--   Let $O$ be a discrete valuation ring which is a domain, and let $E$ be a field equipped with an $O$-algebra structure such that the integral closure $R$ of $O$ in $E$ is a Dedekind domain, finite as an $O$-module, with $E$ as its fraction field. Fix an irreducible element $\varpi$ of $O$, a natural number $n$, and a non-zero prime ideal $\mathfrak P$ of $R$ such that the set of primes of $R$ lying over the maximal ideal $\mathfrak m$ of $O$ is exactly $\{\mathfrak P\}$, with ramification index $e(\mathfrak P \mid \mathfrak m) = n$ and inertia degree $f(\mathfrak P \mid \mathfrak m) = 1$; let $W$ be the valuation subring of $E$ attached to $\mathfrak P$ viewed as a point of the height-one spectrum of $R$. The conclusion is the conjunction of five assertions: (i) any two valuation subrings $W_1, W_2$ of $E$ containing the image of $O$ and sending every element of $\mathfrak m$ into their non-units are equal; (ii) the image of $O$ lies in $W$; (iii) for $x \in O$, the image of $x$ is a non-unit of $W$ if and only if $x \in \mathfrak m$; (iv) every element of $W$ differs from the image of some element of $O$ by a non-unit of $W$; and (v) there are $\pi \in W$ irreducible and a unit $v$ of $W$ with $\varpi = v\,\pi^{n}$ in $E$.
--
--   This is the standard local picture of a totally ramified extension with trivial residue extension: a single prime above $\mathfrak m$ with $e = n$, $f = 1$ forces a unique valuation subring of $E$ over $O$, makes $O$ surject onto its residue field, and writes the uniformiser $\varpi$ as a unit times the $n$-th power of a uniformiser. It is used by [`ValuationSubring.exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq`](thm.html#ValuationSubring.exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq) and by [`ValuationSubring.forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime`](thm.html#ValuationSubring.forall_comap_eq_imp_eq_and_exists_forall_sub_mem_nonunits_of_pow_eq_of_isCoprime) in the construction and recognition of totally ramified extensions of discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (E : Type*) [Field E] [Algebra O E]
    [IsDedekindDomain ↥(integralClosure O E)] [Module.Finite O ↥(integralClosure O E)]
    [IsFractionRing ↥(integralClosure O E) E]
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ)
    (𝔓 : Ideal ↥(integralClosure O E)) [h𝔓 : 𝔓.IsPrime] (h0 : 𝔓 ≠ ⊥)
    (hover : (IsLocalRing.maximalIdeal O).primesOver ↥(integralClosure O E) = {𝔓})
    (he : (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 = n)
    (hf : (IsLocalRing.maximalIdeal O).inertiaDeg' 𝔓 = 1)
    (W : ValuationSubring E)
    (hW : W = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E ⟨𝔓, h𝔓, h0⟩) :

    (∀ W₁ W₂ : ValuationSubring E,
        (∀ x : O, algebraMap O E x ∈ W₁) → (∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O E x ∈ W₁.nonunits) →
        (∀ x : O, algebraMap O E x ∈ W₂) → (∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O E x ∈ W₂.nonunits) →
        W₁ = W₂) ∧

    (∀ x : O, algebraMap O E x ∈ W) ∧
    (∀ x : O, algebraMap O E x ∈ W.nonunits ↔ x ∈ IsLocalRing.maximalIdeal O) ∧

    (∀ e : ↥W, ∃ f : O, (e : E) - algebraMap O E f ∈ W.nonunits) ∧

    (∃ (π : ↥W) (v : (↥W)ˣ), Irreducible π ∧
      algebraMap O E ϖ = ((v : ↥W) : E) * ((π : ↥W) : E) ^ n) := by sorry
