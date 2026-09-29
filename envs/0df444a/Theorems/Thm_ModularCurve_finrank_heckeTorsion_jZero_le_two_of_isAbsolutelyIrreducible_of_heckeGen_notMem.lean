-- Prove2me | Theorems.Thm_ModularCurve_finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_notMem
-- name    : ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/a92c46ce-5cae-531e-a5f3-59f9683e3f9b
-- title:
--   Multiplicity one for J₀(M)[𝔪] in the ordinary case
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime with $p\neq 2$ and $p\nmid M$. Let `HeckeAlg` be the polynomial ring $\mathbb{Z}[X_\ell : \ell\text{ prime}]$, whose generator attached to $\ell$ is `heckeGen`, and let $\mathfrak m$ be a maximal ideal of it containing the image of $p$. Assume given a field $k$, a ring homomorphism $\iota$ from the residue field $\mathrm{HeckeAlg}/\mathfrak m$ to $k$, and a [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22) $\bar\rho$ over $k$, i.e. a $k$-vector space $V$ of rank $2$ together with a monoid homomorphism from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k V$ trivial on the pointwise stabiliser of some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$; assume $\bar\rho$ is absolutely irreducible, meaning that after base change to $\overline{k}$ every invariant submodule is $\bot$ or $\top$. Assume further that for some finite set $S_0\subseteq\mathbb N$ and every prime $\ell\notin S_0$ with $\ell\nmid M$ and $\ell\neq p$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ in the decomposition subgroup of $A$ acting as $x\mapsto x^\ell$ on the residue field of $A$, one has $\mathrm{tr}\,\bar\rho(\sigma)=\iota(X_\ell \bmod \mathfrak m)$; and assume the ordinarity hypothesis $X_p\notin\mathfrak m$. Then, for the `HeckeAlg`-module structure `heckeModuleBar` on $J_0(M)=\mathrm{Pic}^0$ of the level-$M$ modular function field over $\overline{\mathbb Q}$ (given by evaluating the generators at the Hecke correspondences, these being commuting), the submodule of elements annihilated by all of $\mathfrak m$ has dimension at most $2$ over the field $\mathrm{HeckeAlg}/\mathfrak m$.
--
--   This is the multiplicity one statement $\dim_{\mathbb T/\mathfrak m} J_0(M)(\overline{\mathbb Q})[\mathfrak m]\le 2$ for a non-Eisenstein maximal ideal of residue characteristic $p$ odd and prime to the level, in the case where the $p$-th Hecke generator is invertible modulo $\mathfrak m$. It supplies the ordinary branch of the case distinction in [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_notMem.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Residual
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_notMem
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    {k : Type} [Field k] (ι : HeckeAlg ⧸ 𝔪 →+* k)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) (S₀ : Finset ℕ)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)))
    (hord : heckeGen ⟨p, Fact.out⟩ ∉ 𝔪) :
    letI := heckeModuleBar M
    Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪) ≤ 2 := by sorry
