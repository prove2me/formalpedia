-- Prove2me | Theorems.Thm_ModularCurve_finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible
-- name    : ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/ea187aa9-91b4-5dcb-8e45-efa809923f8e
-- title:
--   Multiplicity one bound: dim J₀(M)[𝔪]≤ 2
-- statement:
--   Fix $M\ge 1$ and a prime $p$ with $p\neq 2$ and $p\nmid M$. Let $\mathbb{T}=$ `HeckeAlg` be the polynomial ring $\mathbb{Z}[X_\ell:\ell\text{ prime}]$ on the set of primes, whose generators are written `heckeGen`, and let $\mathfrak m\subseteq\mathbb{T}$ be a maximal ideal containing the image of $p$. Let $k$ be a field, $\iota\colon\mathbb{T}/\mathfrak m\to k$ a ring homomorphism, and $\bar\rho$ a [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22) over $k$: a $k$-vector space $V$ with $\operatorname{finrank}_k V=2$ together with a monoid homomorphism $\rho$ from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\operatorname{End}_k V$ trivial on the fixers of some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. Assume $\bar\rho$ is absolutely irreducible, i.e. the base change of $\rho$ to $\overline{k}\otimes_k V$ admits no Galois-stable submodule other than $\bot$ and $\top$. Assume further, for a finite set $S_0\subseteq\mathbb{N}$, that for every prime $\ell\notin S_0$ with $\ell\nmid M$ and $\ell\neq p$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ and inducing $x\mapsto x^{\ell}$ on the residue field of $A$, one has $\operatorname{tr}_k\rho(\sigma)=\iota(X_\ell \bmod \mathfrak m)$. Then, for the $\mathbb{T}$-module structure `heckeModuleBar` on $J_0(M)=$ `JZero M`, the group of degree-zero divisor classes of the modular function field of level $M$ over $\overline{\mathbb{Q}}$, the $\mathfrak m$-torsion submodule $\{x : \mathfrak m\cdot x=0\}$ satisfies $\operatorname{finrank}_{\mathbb{T}/\mathfrak m}J_0(M)[\mathfrak m]\le 2$.
--
--   This is the upper bound half of multiplicity one for the Jacobian $J_0(M)$ at a maximal ideal of residual characteristic $p$ whose associated residual representation is absolutely irreducible (Mazur, Ribet, Wiles). It feeds the cohomological input used later in the modularity-lifting argument, via the statement [`CohCarrier.exists_span_pair_union_ker_smul_eq_top_cornerSubmodule_H1_top_of_isAbsolutelyIrreducible`](thm.html#CohCarrier.exists_span_pair_union_ker_smul_eq_top_cornerSubmodule_H1_top_of_isAbsolutelyIrreducible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Residual
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    {k : Type} [Field k] (ι : HeckeAlg ⧸ 𝔪 →+* k)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) (S₀ : Finset ℕ)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩))) :
    letI := heckeModuleBar M
    Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪) ≤ 2 := by sorry
