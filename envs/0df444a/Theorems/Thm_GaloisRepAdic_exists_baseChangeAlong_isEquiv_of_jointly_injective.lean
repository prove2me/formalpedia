-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_jointly_injective
-- name    : GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_jointly_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/2716675c-d1b6-5a41-8809-242f180a81d9
-- title:
--   Carayol descent for a jointly faithful family of T-algebras
-- statement:
--   Let $T$ be a noetherian local commutative ring, complete with respect to its maximal ideal and with finite residue field, and let $A_0,\dots,A_{n-1}$ be local commutative rings which are $T$-algebras, module-finite over $T$, whose structure maps $\varphi_i =$ `algebraMap T (A i)` are local homomorphisms and are jointly injective, in the sense that an $x \in T$ with $\varphi_i(x) = 0$ for all $i$ vanishes. Let $\bar\rho$ be a residual representation over the residue field of $T$, i.e. a two-dimensional vector space with a monoid homomorphism from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ to its endomorphisms factoring through a finite level, and assume $\bar\rho$ becomes irreducible over an algebraic closure of the residue field. For each $i$ let $\rho_i$ be an adic Galois representation over $A_i$: a free $A_i$-module of rank two carrying a Galois action that is $\mathfrak m_{A_i}$-adically continuous (for each $m$ some finite subextension $L/\mathbb Q$ has the property that elements fixing $L$ pointwise act trivially modulo $\mathfrak m_{A_i}^m$), and assume the residual representation $\operatorname{ResidueField}(A_i) \otimes_{A_i} \rho_i$ is equivalent to the base change of $\bar\rho$ along the induced map of residue fields. Finally let $S_0$ be a finite set of natural numbers and, for every prime $\ell \notin S_0$, let $\tau_\ell \in T$ be an element such that for every valuation subring $P$ of $\overline{\mathbb Q}$ with $\ell$ a nonunit of $P$ and every $\sigma$ lying in the decomposition subgroup of $P$ and acting on the residue field of $P$ by $x \mapsto x^{\ell}$, one has $\operatorname{tr}\rho_i(\sigma) = \varphi_i(\tau_\ell)$ for all $i$. The conclusion is that there exists an adic Galois representation $\rho'$ over $T$ such that, for each $i$, the base change of $\rho'$ along $\varphi_i$ is equivalent to $\rho_i$ (an $A_i$-linear isomorphism commuting with the Galois actions), the residual representation of $\rho'$ is equivalent to $\bar\rho$, and $\operatorname{tr}\rho'(\sigma) = \tau_\ell$ for every prime $\ell \notin S_0$ and every Frobenius element $\sigma$ at a place above $\ell$ in the above sense.
--
--   This is the descent theorem of Carayol (after Serre), producing a two-dimensional Galois representation over a complete noetherian local ring from a jointly faithful finite family of such representations over module-finite local algebras, given absolutely irreducible reduction and Frobenius traces already lying in the base ring; here the trace hypothesis is imposed only at Frobenius elements outside a finite set of primes, the general trace condition being recovered by Chebotarev density. It is used to construct the Galois representation attached to a Hecke ring whose Frobenius traces are the Hecke operators $T_\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_jointly_injective.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_jointly_injective
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (maximalIdeal T) T] [Finite (ResidueField T)]
    {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Algebra T (A i)] [∀ i, Module.Finite T (A i)]
    [hloc : ∀ i, IsLocalHom (algebraMap T (A i))]
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0)
    (ρbar : ResidualGaloisRep (ResidueField T)) (habs : ρbar.IsAbsolutelyIrreducible)
    (ρ : ∀ i, GaloisRepAdic (A i))
    (hres : ∀ i, (ρ i).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap T (A i)))))
    (S₀ : Finset ℕ) (τ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → T)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          ∀ i, (ρ i).trace σ = algebraMap T (A i) (τ ℓ hℓ hℓS)) :
    ∃ ρ' : GaloisRepAdic T,

      (∀ i, ((ρ'.baseChangeAlong (algebraMap T (A i)) (hloc i)).IsEquiv (ρ i))) ∧

      ρ'.residual.IsEquiv ρbar ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
            ρ'.trace σ = τ ℓ hℓ hℓS) := by sorry
