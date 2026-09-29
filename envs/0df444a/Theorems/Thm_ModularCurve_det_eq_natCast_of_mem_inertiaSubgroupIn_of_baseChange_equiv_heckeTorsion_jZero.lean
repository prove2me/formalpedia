-- Prove2me | Theorems.Thm_ModularCurve_det_eq_natCast_of_mem_inertiaSubgroupIn_of_baseChange_equiv_heckeTorsion_jZero
-- name    : ModularCurve.det_eq_natCast_of_mem_inertiaSubgroupIn_of_baseChange_equiv_heckeTorsion_jZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/c6102522-863e-5697-9e05-eae035c93134
-- title:
--   Determinant of inertia at p on 𝔪-torsion equals a
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime with $p\neq 2$ and $p\nmid M$. Let $\mathfrak m$ be a maximal ideal of the Hecke algebra `HeckeAlg`, the polynomial ring $\mathbb Z[X_\ell]$ on variables indexed by the primes, with the image of $p$ lying in $\mathfrak m$; let $k$ be a field and $\iota\colon \mathrm{HeckeAlg}/\mathfrak m \to k$ a ring homomorphism. Let $\bar\rho$ be a residual Galois representation over $k$, that is a two-dimensional $k$-vector space $\bar\rho.V$ together with a monoid homomorphism $\bar\rho.\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k(\bar\rho.V)$ trivial on the automorphisms fixing some finite subextension of $\overline{\mathbb Q}/\mathbb Q$ pointwise, and assume $\bar\rho$ is absolutely irreducible, i.e. its base change to $\overline{k}$ has no invariant subspace other than $\bot$ and $\top$. Let $S_0$ be a finite set of naturals and assume that for every prime $\ell\notin S_0$ with $\ell\nmid M$, $\ell\neq p$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ and inducing $x\mapsto x^{\ell}$ on the residue field of $A$, one has $\mathrm{tr}\,\bar\rho.\rho(\sigma)=\iota(X_\ell \bmod \mathfrak m)$. Equip $J_0(M)=\mathrm{Pic}^0$ of the modular function field over $\overline{\mathbb Q}$ of level $M$ with the Hecke module structure `heckeModuleBar`, and assume the Galois and Hecke actions on it commute. Let $V$ be an $\mathrm{HeckeAlg}/\mathfrak m$-submodule of the $\mathfrak m$-torsion $J_0(M)[\mathfrak m]$, let $\sigma V$ be a monoid homomorphism from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_{\mathrm{HeckeAlg}/\mathfrak m}(V)$ whose values agree with the Galois action on $\mathfrak m$-torsion, assume $V$ has rank $2$ over $\mathrm{HeckeAlg}/\mathfrak m$, and let $e\colon k\otimes_{\mathrm{HeckeAlg}/\mathfrak m} V\to \bar\rho.V$ be a $k$-linear isomorphism (via the algebra structure given by $\iota$) satisfying $e(c\otimes \sigma V(\sigma)v)=\bar\rho.\rho(\sigma)\,e(c\otimes v)$. Finally let $A$ be a valuation subring of $\overline{\mathbb Q}$ in which $p$ is a non-unit, let $\sigma$ lie in the image in $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup of $A$, and let $a\in\mathbb N$ satisfy $\sigma\mu=\mu^a$ for every $\mu\in\overline{\mathbb Q}$ with $\mu^p=1$. Then the determinant of $\sigma V(\sigma)$ as an $\mathrm{HeckeAlg}/\mathfrak m$-linear endomorphism of $V$ is the image of $a$ in $\mathrm{HeckeAlg}/\mathfrak m$.
--
--   This is the weight-two determinant identity $\det\bar\rho=\chi$ for the mod-$p$ cyclotomic character $\chi$, restricted to inertia at $p$ and formulated for the copy of $\bar\rho$ carried by an $\mathfrak m$-torsion plane in $J_0(M)(\overline{\mathbb Q})$; it rests on the Eichler–Shimura relation for $J_0(M)$ together with the Frobenius trace hypothesis. It is used in the study of the reduction maps `reductionModL` attached to such planes, namely in [`ModularCurve.eq_top_of_sup_ker_reductionModL_eq_top_of_baseChange_equiv_of_isAbsolutelyIrreducible`](thm.html#ModularCurve.eq_top_of_sup_ker_reductionModL_eq_top_of_baseChange_equiv_of_isAbsolutelyIrreducible) and [`ModularCurve.not_le_ker_reductionModL_of_baseChange_equiv_of_isAbsolutelyIrreducible_of_heckeGen_notMem`](thm.html#ModularCurve.not_le_ker_reductionModL_of_baseChange_equiv_of_isAbsolutelyIrreducible_of_heckeGen_notMem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_det_eq_natCast_of_mem_inertiaSubgroupIn_of_baseChange_equiv_heckeTorsion_jZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.det_eq_natCast_of_mem_inertiaSubgroupIn_of_baseChange_equiv_heckeTorsion_jZero
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpM : ¬ p ∣ M)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    {k : Type} [Field k] (ι : HeckeAlg ⧸ 𝔪 →+* k)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) (S₀ : Finset ℕ)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)))
    (hsmc : letI := heckeModuleBar M
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero M))
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
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (a : ℕ) (ha : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) :
    letI := heckeModuleBar M; haveI := hsmc
    LinearMap.det ((σV σ : Module.End (HeckeAlg ⧸ 𝔪) ↥V) : ↥V →ₗ[HeckeAlg ⧸ 𝔪] ↥V) = (a : HeckeAlg ⧸ 𝔪) := by sorry
