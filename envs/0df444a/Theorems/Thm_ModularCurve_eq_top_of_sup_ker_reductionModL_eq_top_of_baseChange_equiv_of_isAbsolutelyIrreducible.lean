-- Prove2me | Theorems.Thm_ModularCurve_eq_top_of_sup_ker_reductionModL_eq_top_of_baseChange_equiv_of_isAbsolutelyIrreducible
-- name    : ModularCurve.eq_top_of_sup_ker_reductionModL_eq_top_of_baseChange_equiv_of_isAbsolutelyIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/6a978541-1e83-59fe-9449-2aaf31dfee82
-- title:
--   Reduction kernel forces V=J₀(M)(ℚ̄)[𝔪]
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime with $p\neq 2$ and $p\nmid M$. Let $\mathfrak m$ be a maximal ideal of `HeckeAlg`, the polynomial ring $\mathbb Z[X_\ell]$ on indeterminates indexed by the primes, with `heckeGen ℓ` $=X_\ell$, and suppose the image of $p$ lies in $\mathfrak m$ while $X_p\notin\mathfrak m$. Let $k$ be a field, $\iota\colon$ `HeckeAlg`$/\mathfrak m\to k$ a ring homomorphism, and $\bar\rho$ a residual Galois representation over $k$: a two-dimensional $k$-space $\bar\rho.V$ with a multiplicative map $\bar\rho.\rho$ from $\mathrm{Gal}(\bar{\mathbb Q}/\mathbb Q)=\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k(\bar\rho.V)$ trivial on the automorphisms fixing some finite extension of $\mathbb Q$ pointwise; assume $\bar\rho$ is absolutely irreducible, i.e. its base change to $\overline{k}$ has no stable submodule other than $0$ and everything. Assume, for a finite set $S_0$ of naturals, that for every prime $\ell\notin S_0$ with $\ell\nmid M$, $\ell\neq p$, every valuation subring $A$ of $\bar{\mathbb Q}$ with $\ell$ a nonunit of $A$ and every $\sigma$ in the decomposition group of $A$ acting on the residue field by $x\mapsto x^{\ell}$, one has $\mathrm{tr}\,\bar\rho.\rho(\sigma)=\iota(X_\ell\bmod\mathfrak m)$. Let $J_0(M)$ denote the degree-zero divisor class group of the modular function field of level $M$ over $\bar{\mathbb Q}$, with its `heckeModuleBar` `HeckeAlg`-module structure, and assume the Galois and Hecke actions on it commute. Fix a valuation subring $A$ of $\bar{\mathbb Q}$ in which $p$ is a nonunit, and let $K$ and $V$ be `HeckeAlg`$/\mathfrak m$-submodules of the $\mathfrak m$-torsion $J_0(M)[\mathfrak m]$, with $K$ characterised as the set of $w$ with $\mathrm{red}_A(w)=0$ under reduction along $A$ to the degree-zero class group over the residue field of $A$. Suppose $V$ carries a multiplicative action $\sigma_V$ of the Galois group by `HeckeAlg`$/\mathfrak m$-endomorphisms agreeing with the Galois action on $J_0(M)[\mathfrak m]$, that $V$ has rank $2$ over `HeckeAlg`$/\mathfrak m$, and that there is a $k$-linear isomorphism $e\colon k\otimes_{\mathrm{HeckeAlg}/\mathfrak m}V\to\bar\rho.V$ ($k$ an algebra via $\iota$) with $e(c\otimes\sigma_V(\sigma)v)=\bar\rho.\rho(\sigma)e(c\otimes v)$. Then $V\sqcup K=J_0(M)[\mathfrak m]$ implies $V=J_0(M)[\mathfrak m]$.
--
--   This is the ordinary, non-Eisenstein step which upgrades the statement that a Galois-stable copy $V$ of $\bar\rho$ together with the kernel of reduction at a place above $p$ spans $J_0(M)(\bar{\mathbb Q})[\mathfrak m]$ to the statement that $V$ exhausts it. It feeds into the multiplicity-one bound [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_notMem`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_notMem), that $J_0(M)(\bar{\mathbb Q})[\mathfrak m]$ has rank at most $2$ over $\mathbb T/\mathfrak m$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_top_of_sup_ker_reductionModL_eq_top_of_baseChange_equiv_of_isAbsolutelyIrreducible.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.eq_top_of_sup_ker_reductionModL_eq_top_of_baseChange_equiv_of_isAbsolutelyIrreducible
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    {k : Type} [Field k] (ι : HeckeAlg ⧸ 𝔪 →+* k)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) (S₀ : Finset ℕ)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)))
    (hord : heckeGen ⟨p, Fact.out⟩ ∉ 𝔪)
    (hsmc : letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (K : letI := heckeModuleBar M; Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪))
    (hK : letI := heckeModuleBar M
      ∀ w : ↥(heckeTorsion (JZero M) 𝔪), w ∈ K ↔ reductionModL A M (w : JZero M) = 0)
    (V : letI := heckeModuleBar M; Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero M) 𝔪))
    (σV : letI := heckeModuleBar M; haveI := hsmc
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End (HeckeAlg ⧸ 𝔪) ↥V)
    (hσV : letI := heckeModuleBar M; haveI := hsmc
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥V),
        ((σV σ v : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) =
          mTorsionGaloisRep (JZero M) 𝔪 σ (v : ↥(heckeTorsion (JZero M) 𝔪)))
    (hV2 : letI := heckeModuleBar M; Module.finrank (HeckeAlg ⧸ 𝔪) ↥V = 2)
    (e : letI := heckeModuleBar M; letI := ι.toAlgebra; TensorProduct (HeckeAlg ⧸ 𝔪) k ↥V ≃ₗ[k] ρbar.V)
    (he : letI := heckeModuleBar M; letI := ι.toAlgebra
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : k) (v : ↥V),
        e (c ⊗ₜ[HeckeAlg ⧸ 𝔪] σV σ v) = ρbar.ρ σ (e (c ⊗ₜ[HeckeAlg ⧸ 𝔪] v)))
    (hsup : letI := heckeModuleBar M; V ⊔ K = ⊤) :
    letI := heckeModuleBar M
    V = ⊤ := by sorry
