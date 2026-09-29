-- Prove2me | Theorems.Thm_ModularCurve_finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem
-- name    : ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/5ae3e36a-dcc0-585e-9725-8927531c77ea
-- title:
--   Multiplicity one for J₀(M)[𝔪] when Tₚ ∈ 𝔪
-- statement:
--   Let $M \ge 1$ and let $p$ be a prime with $p \neq 2$ and $p \nmid M$. Write $\mathbb{T} = \mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbb{Z}$ for the polynomial ring on one generator $\mathrm{heckeGen}\,\ell = X_\ell$ per prime $\ell$, and let $\mathfrak m \subseteq \mathbb{T}$ be a maximal ideal containing the image of $p$ and containing $X_p$. Let $k$ be a field, $\iota : \mathbb{T}/\mathfrak m \to k$ a ring homomorphism, and $\bar\rho$ a residual Galois representation over $k$: a $k$-vector space $V$ of dimension $2$ with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{End}_k V$ trivial on the automorphisms fixing some finite subextension $L/\mathbb{Q}$ of $\overline{\mathbb{Q}}$. Assume $\bar\rho$ is absolutely irreducible, i.e. every submodule of $\mathrm{AlgebraicClosure}\,k \otimes_k V$ stable under the base-changed action is $\bot$ or $\top$. Assume further, for a finite set $S_0$ of naturals, that for every prime $\ell \notin S_0$ with $\ell \nmid M$ and $\ell \neq p$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, one has $\mathrm{tr}\,\rho(\sigma) = \iota(X_\ell \bmod \mathfrak m)$. Then, for the $\mathbb{T}$-module structure `heckeModuleBar M` on $\mathrm{JZero}\,M$, the group of degree-zero divisor classes modulo principal divisors of the base-changed modular function field of level $M$ over $\overline{\mathbb{Q}}$, the submodule of elements annihilated by all of $\mathfrak m$ has $\mathbb{T}/\mathfrak m$-dimension at most $2$.
--
--   This is the multiplicity one statement for $J_0(M)(\overline{\mathbb{Q}})[\mathfrak m]$ at a non-Eisenstein maximal ideal of residue characteristic $p$, in the case $T_p \in \mathfrak m$ (the supersingular case of Mazur's argument). It is one of the two cases combined in [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible), which in turn feeds the Galois-cohomological input to the level-lowering and lifting arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Residual
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    {k : Type} [Field k] (ι : HeckeAlg ⧸ 𝔪 →+* k)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) (S₀ : Finset ℕ)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)))
    (hss : heckeGen ⟨p, Fact.out⟩ ∈ 𝔪) :
    letI := heckeModuleBar M
    Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪) ≤ 2 := by sorry
