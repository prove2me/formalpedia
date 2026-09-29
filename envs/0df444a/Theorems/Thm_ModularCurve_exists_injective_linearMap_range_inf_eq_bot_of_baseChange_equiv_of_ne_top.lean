-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_linearMap_range_inf_eq_bot_of_baseChange_equiv_of_ne_top
-- name    : ModularCurve.exists_injective_linearMap_range_inf_eq_bot_of_baseChange_equiv_of_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/b7ac1317-864e-564a-aa0f-c254adb56b4b
-- title:
--   Boston–Lenstra–Ribet: a second copy of ρ̄ in J₀(M)[𝔪]
-- statement:
--   Let $M \geq 1$ and let $p$ be an odd prime not dividing $M$. Let $\mathbb{T} =$ `HeckeAlg` be the polynomial ring $\mathbb{Z}[X_\ell]$ over the primes, with generators $T_\ell =$ `heckeGen` $\ell$, let $\mathfrak{m} \subset \mathbb{T}$ be a maximal ideal containing the image of $p$, let $k$ be a field and $\iota : \mathbb{T}/\mathfrak{m} \to k$ a ring homomorphism. Let $\bar\rho$ be a residual Galois representation over $k$, i.e. a two-dimensional $k$-vector space $\bar\rho.V$ with a monoid homomorphism $\bar\rho.\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathrm{End}_k(\bar\rho.V)$ that is trivial on the automorphisms fixing some finite-dimensional intermediate field; assume $\bar\rho$ absolutely irreducible, in the sense that its base change to $\overline{k}$ has no Galois-stable submodule other than $\bot$ and $\top$. Let $S_0$ be a finite set of naturals and assume that for every prime $\ell \notin S_0$ with $\ell \nmid M$, $\ell \neq p$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$ and every $\sigma$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^\ell$, one has $\mathrm{tr}\, \bar\rho.\rho(\sigma) = \iota(T_\ell \bmod \mathfrak m)$. Give $J_0(M) :=$ `JZero M`, the degree-zero divisor class group of the base-changed modular function field of level $M$ over $\overline{\mathbb Q}$, its $\mathbb{T}$-module structure `heckeModuleBar M`, and assume the Galois and Hecke actions commute. Let $V$ be a $\mathbb{T}/\mathfrak{m}$-submodule of the $\mathfrak{m}$-torsion $J_0(M)[\mathfrak m]$, let $\sigma V$ be a monoid homomorphism from the Galois group to $\mathrm{End}_{\mathbb{T}/\mathfrak{m}}(V)$ whose action on elements of $V$ agrees with the Galois action `mTorsionGaloisRep` on the $\mathfrak m$-torsion, assume $\dim_{\mathbb{T}/\mathfrak m} V = 2$, and let $e$ be a $k$-linear isomorphism $k \otimes_{\mathbb{T}/\mathfrak m} V \simeq \bar\rho.V$ (with $k$ a $\mathbb{T}/\mathfrak{m}$-algebra via $\iota$) satisfying $e(c \otimes \sigma V(\sigma) v) = \bar\rho.\rho(\sigma)(e(c \otimes v))$ for all $\sigma$, $c \in k$, $v \in V$. Assume finally $V \neq J_0(M)[\mathfrak m]$. Then there exists a $\mathbb{T}/\mathfrak{m}$-linear map $f : V \to J_0(M)[\mathfrak m]$ that is injective, satisfies $\mathrm{range}(f) \cap V = 0$, and is Galois-equivariant: $f(\sigma V(\sigma) v) = \sigma \cdot f(v)$ for all $\sigma$ and $v \in V$.
--
--   This is the form of the Boston–Lenstra–Ribet theorem used in the multiplicity-one argument: the $\mathfrak m$-torsion of $J_0(M)$ over $\overline{\mathbb Q}$ is built from copies of $\bar\rho$, so a Galois-stable plane $V$ realising $\bar\rho$ which is not the whole $\mathfrak m$-torsion admits a second, disjoint, equivariant copy of itself, giving $\bar\rho \oplus \bar\rho$ inside $J_0(M)[\mathfrak m]$. It is invoked in the proof that a certain sum of kernels of reduction maps is everything ([`ModularCurve.eq_top_of_sup_ker_reductionModL_eq_top_of_baseChange_equiv_of_isAbsolutelyIrreducible`](thm.html#ModularCurve.eq_top_of_sup_ker_reductionModL_eq_top_of_baseChange_equiv_of_isAbsolutelyIrreducible)), and it rests on the decomposition result [`ModularCurve.exists_blrDecomposition_heckeTorsion_of_span_eq_top_of_frobeniusQuadratic_of_dense`](thm.html#ModularCurve.exists_blrDecomposition_heckeTorsion_of_span_eq_top_of_frobeniusQuadratic_of_dense) together with Čebotarev-type density of Frobenius elements and finiteness of $p$-power torsion on $J_0(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_linearMap_range_inf_eq_bot_of_baseChange_equiv_of_ne_top.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.exists_injective_linearMap_range_inf_eq_bot_of_baseChange_equiv_of_ne_top
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
    (hVtop : letI := heckeModuleBar M; V ≠ ⊤) :
    letI := heckeModuleBar M; haveI := hsmc
    ∃ f : ↥V →ₗ[HeckeAlg ⧸ 𝔪] ↥(heckeTorsion (JZero M) 𝔪),
      Function.Injective f ∧ LinearMap.range f ⊓ V = ⊥ ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥V),
        f (σV σ v) = mTorsionGaloisRep (JZero M) 𝔪 σ (f v) := by sorry
