-- Prove2me | Theorems.Thm_ModularCurve_exists_bilinForm_heckeTorsion_jZero_nondegenerate_smul_eq_cyclotomic_of_baseChange_equiv
-- name    : ModularCurve.exists_bilinForm_heckeTorsion_jZero_nondegenerate_smul_eq_cyclotomic_of_baseChange_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/0a95f423-44c0-5ddb-9674-9643ee9f0b91
-- title:
--   Cyclotomic-equivariant nondegenerate pairing on a Galois plane in J₀(M)[𝔪]
-- statement:
--   Let $M \ge 1$, let $p$ be a prime with $p \neq 2$ and $p \nmid M$, and let $\mathfrak m$ be a maximal ideal of the Hecke algebra `HeckeAlg` $= \mathbb Z[X_\ell : \ell \text{ prime}]$ containing the image of $p$, so that $\kappa :=$ `HeckeAlg`$/\mathfrak m$ is a field. Let $k$ be a field, $\iota : \kappa \to k$ a ring homomorphism, and $\rho bar$ a residual Galois representation over $k$, i.e. a two-dimensional $k$-space $\rho bar.V$ with a monoid homomorphism $\rho bar.\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ to $\mathrm{End}_k(\rho bar.V)$ trivial on the automorphisms fixing some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$; assume $\rho bar$ becomes irreducible over $\mathrm{AlgebraicClosure}\,k$. Let $S_0$ be a finite set of naturals and assume that for every prime $\ell \notin S_0$ with $\ell \nmid M$, $\ell \neq p$, every valuation subring $A \subseteq \overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, and every $\sigma$ acting on the residue field of $A$ by $x \mapsto x^{\ell}$ within the decomposition subgroup, one has $\mathrm{tr}\,\rho bar.\rho(\sigma) = \iota(X_\ell \bmod \mathfrak m)$. Equip $J_0(M) := \mathrm{Pic}^0$ of the base-changed modular function field of level $M$ over $\overline{\mathbb Q}$ with the Hecke module structure `heckeModuleBar M`, and assume the Galois and Hecke actions on it commute. Let $V$ be a $\kappa$-submodule of the $\mathfrak m$-torsion $J_0(M)[\mathfrak m]$ with $\dim_\kappa V = 2$, let $\sigma V$ be a monoid homomorphism from the Galois group to $\mathrm{End}_\kappa(V)$ whose underlying action on $J_0(M)[\mathfrak m]$ is the natural Galois action `mTorsionGaloisRep`, and let $e : k \otimes_\kappa V \simeq \rho bar.V$ be a $k$-linear isomorphism (with $k$ a $\kappa$-algebra via $\iota$) satisfying $e(c \otimes \sigma V(\sigma)v) = \rho bar.\rho(\sigma)\,e(c \otimes v)$ for all $\sigma$, $c \in k$, $v \in V$. Then there is a $\kappa$-bilinear form $B : V \times V \to \kappa$ that is nondegenerate in the first variable (if $B(x,y) = 0$ for all $y$ then $x = 0$) and satisfies, for every Galois element $\sigma$ and every natural number $a$ such that $\sigma\mu = \mu^a$ for all $\mu \in \overline{\mathbb Q}$ with $\mu^p = 1$, the identity $B(\sigma V(\sigma)x, \sigma V(\sigma)y) = a \cdot B(x,y)$ for all $x, y \in V$, the scalar being the image of $a$ in $\kappa$.
--
--   This is the statement that the determinant of a Galois-stable $\kappa$-plane inside $J_0(M)(\overline{\mathbb Q})[\mathfrak m]$ is the mod-$p$ cyclotomic character, packaged as the existence of a nondegenerate $\kappa$-bilinear form on which Galois acts by that character; the trace condition identifying Frobenius traces with the Hecke generators is the Eichler–Shimura input. It feeds the bound $\dim_\kappa J_0(M)[\mathfrak m] \le 2$ in [`ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem`](thm.html#ModularCurve.finrank_heckeTorsion_jZero_le_two_of_isAbsolutelyIrreducible_of_heckeGen_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bilinForm_heckeTorsion_jZero_nondegenerate_smul_eq_cyclotomic_of_baseChange_equiv.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Residual
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve in
open scoped TensorProduct in

theorem ModularCurve.exists_bilinForm_heckeTorsion_jZero_nondegenerate_smul_eq_cyclotomic_of_baseChange_equiv
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
    (σV : letI := heckeModuleBar M
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End (HeckeAlg ⧸ 𝔪) ↥V)
    (hσV : letI := heckeModuleBar M; haveI := hsmc
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ↥V),
        ((σV σ v : ↥V) : ↥(heckeTorsion (JZero M) 𝔪)) =
          mTorsionGaloisRep (JZero M) 𝔪 σ (v : ↥(heckeTorsion (JZero M) 𝔪)))
    (hfin : letI := heckeModuleBar M; Module.finrank (HeckeAlg ⧸ 𝔪) ↥V = 2)
    (e : letI := heckeModuleBar M; letI := ι.toAlgebra; (k ⊗[HeckeAlg ⧸ 𝔪] ↥V) ≃ₗ[k] ρbar.V)
    (he : letI := heckeModuleBar M; letI := ι.toAlgebra
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : k) (v : ↥V),
        e (c ⊗ₜ σV σ v) = ρbar.ρ σ (e (c ⊗ₜ v))) :
    letI := heckeModuleBar M
    ∃ B : ↥V →ₗ[HeckeAlg ⧸ 𝔪] ↥V →ₗ[HeckeAlg ⧸ 𝔪] (HeckeAlg ⧸ 𝔪),
      (∀ x : ↥V, (∀ y : ↥V, B x y = 0) → x = 0) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
          ∀ x y : ↥V, B (σV σ x) (σV σ y) = (a : HeckeAlg ⧸ 𝔪) • B x y) := by sorry
