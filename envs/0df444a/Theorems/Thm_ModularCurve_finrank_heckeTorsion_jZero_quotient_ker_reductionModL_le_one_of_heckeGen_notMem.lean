-- Prove2me | Theorems.Thm_ModularCurve_finrank_heckeTorsion_jZero_quotient_ker_reductionModL_le_one_of_heckeGen_notMem
-- name    : ModularCurve.finrank_heckeTorsion_jZero_quotient_ker_reductionModL_le_one_of_heckeGen_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/181645f8-47b6-55a5-afe3-b68a6fa64a84
-- title:
--   Rank at most one for 𝔪-torsion modulo the reduction kernel
-- statement:
--   Fix an integer $M\ge 1$ and an odd prime $p$ with $p\nmid M$. Let $\mathbb T=$ `HeckeAlg` be the polynomial ring $\mathbb Z[X_\ell]$ over the primes $\ell$, with generators `heckeGen` $\ell = X_\ell$, and let $\mathfrak m\subset\mathbb T$ be a maximal ideal containing the image of $p$. Let $k$ be a field, $\iota\colon\mathbb T/\mathfrak m\to k$ a ring homomorphism, and $\bar\rho$ a [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22) over $k$: a $2$-dimensional $k$-space $V$ together with a monoid homomorphism $\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k V$ that is trivial on the subgroup fixing some finite-dimensional intermediate field; assume $\bar\rho$ is absolutely irreducible, i.e. after base change to $\overline{k}$ the only Galois-stable submodules are $\bot$ and $\top$. Let $S_0$ be a finite set of naturals and assume the eigensystem is attached: for every prime $\ell\notin S_0$ with $\ell\nmid M$, $\ell\ne p$, every valuation subring $A'$ of $\overline{\mathbb Q}$ with $\ell$ a nonunit of $A'$ and every $\sigma$ lying in the decomposition subgroup of $A'$ and acting on the residue field by $x\mapsto x^{\ell}$, one has $\mathrm{tr}\,\bar\rho(\sigma)=\iota(X_\ell \bmod \mathfrak m)$. Assume further the ordinarity condition $X_p\notin\mathfrak m$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$. Give $J_0(M)=$ `JZero M`, the degree-zero Picard group of the modular function field over $\overline{\mathbb Q}$, the $\mathbb T$-module structure `heckeModuleBar M`, and let $K$ be a $\mathbb T/\mathfrak m$-submodule of the $\mathfrak m$-torsion $J_0(M)[\mathfrak m]$ consisting exactly of those $w$ with $\mathrm{red}_A(w)=0$, reduction being `reductionModL` along the residue map of $A$. Then $J_0(M)[\mathfrak m]/K$ has $\mathbb T/\mathfrak m$-rank at most $1$.
--
--   This is the multiplicity-one statement of Mazur's Corollary 14.8 in the shape used by the ordinary argument: the étale part of the $\mathfrak m$-torsion of $J_0(M)$, realised as the image of $J_0(M)[\mathfrak m]$ under reduction at a place above $p$, has rank at most one over the residue field $\mathbb T/\mathfrak m$. It is the ordinary half of the proof that $J_0(M)[\mathfrak m]$ itself has $\mathbb T/\mathfrak m$-rank at most two, cited by [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_notMem`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_notMem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_heckeTorsion_jZero_quotient_ker_reductionModL_le_one_of_heckeGen_notMem.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.finrank_heckeTorsion_jZero_quotient_ker_reductionModL_le_one_of_heckeGen_notMem
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    {k : Type} [Field k] (ι : HeckeAlg ⧸ 𝔪 →+* k)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) (S₀ : Finset ℕ)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)))
    (hord : heckeGen ⟨p, Fact.out⟩ ∉ 𝔪)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (K : letI := heckeModuleBar M; Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪))
    (hK : letI := heckeModuleBar M
      ∀ w : ↥(heckeTorsion (JZero M) 𝔪), w ∈ K ↔ reductionModL A M (w : JZero M) = 0) :
    letI := heckeModuleBar M
    Module.finrank (HeckeAlg ⧸ 𝔪) (↥(heckeTorsion (JZero M) 𝔪) ⧸ K) ≤ 1 := by sorry
