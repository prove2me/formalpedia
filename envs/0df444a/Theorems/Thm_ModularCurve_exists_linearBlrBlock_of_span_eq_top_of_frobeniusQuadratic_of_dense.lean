-- Prove2me | Theorems.Thm_ModularCurve_exists_linearBlrBlock_of_span_eq_top_of_frobeniusQuadratic_of_dense
-- name    : ModularCurve.exists_linearBlrBlock_of_span_eq_top_of_frobeniusQuadratic_of_dense
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/ccc47e9d-cc8b-5c13-9917-10055e14d0b1
-- title:
--   A Galois-stable copy of ρ inside J[𝔪]
-- statement:
--   Let $J$ be an abelian group carrying a module structure over `HeckeAlg` $=\mathbb Z[X_\ell : \ell \text{ prime}]$ (the polynomial ring on the primes, with $X_\ell$ written `heckeGen`) together with a distributive action of $G=\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ commuting with the `HeckeAlg`-action. Fix naturals $N,p$ and a maximal ideal $\mathfrak m$ of `HeckeAlg` containing the image of $p$, write $k=$ `HeckeAlg`$/\mathfrak m$, and let $\rho : G \to M_2(k)$ be a monoid homomorphism with $2 \neq 0$ in $k$ and whose image spans $M_2(k)$ as a $k$-module. Assume `FrobeniusQuadratic`: for every prime $\ell \nmid Np$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, every $\sigma$ lying in the decomposition subgroup of $A$ and acting as $x \mapsto x^{\ell}$ on the residue field, and every $x \in J$ killed by a power of $p$, one has $\sigma^2 x - X_\ell\cdot(\sigma x) + \ell x = 0$. Let $S$ be a finite set of naturals such that every prime outside $S$ fails to divide $Np$, and assume that for each prime $\ell \notin S$ and each such $A$ and Frobenius $\sigma$ at $\ell$ the class of $X_\ell$ in $k$ equals $\operatorname{tr} \rho(\sigma)$ and the class of $\ell$ equals $\det \rho(\sigma)$. Assume [`FrobeniusPowerDense`](def/GaloisRep_FrobeniusPowerDense.html#L7) for the subgroup $H = \ker \rho \cap \{\text{elements fixing } J[\mathfrak m] \text{ pointwise}\}$, i.e. every $\sigma \in G$ satisfies $g\tau^n g^{-1}\sigma^{-1} \in H$ for some prime $\ell \notin S$, some valuation subring over $\ell$, some Frobenius $\tau$ at $\ell$, some $g \in G$ and some $n$. Finally let $J[\mathfrak m] =$ `heckeTorsion J 𝔪`, the submodule of elements annihilated by $\mathfrak m$, be finite and nonzero. Then there is an injective $k$-linear map $\iota : k^2 \to J[\mathfrak m]$ with $\iota(\rho(\sigma)v) = \sigma \cdot \iota(v)$ for all $\sigma \in G$ and $v \in k^2$, the action on $J[\mathfrak m]$ being `mTorsionGaloisRep`.
--
--   This is the multiplicity-one style input of Boston–Lenstra–Ribet in the form needed for level lowering: under the stated trace/determinant conditions at Frobenius elements, a nonzero $\mathfrak m$-torsion module contains $\rho$ as a $k[G]$-submodule. It feeds the construction of a two-dimensional Galois-stable subspace of the $\mathfrak m$-torsion of the Jacobian used further on in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearBlrBlock_of_span_eq_top_of_frobeniusQuadratic_of_dense.lean

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_linearBlrBlock_of_span_eq_top_of_frobeniusQuadratic_of_dense {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (h2 : (2 : HeckeAlg ⧸ 𝔪) ≠ 0)
    (hspan : Submodule.span (HeckeAlg ⧸ 𝔪)
      (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g)) = ⊤)
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧
          Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (heckeTorsion J 𝔪 : Set J)))
    (hfin : Finite (heckeTorsion J 𝔪)) (hne : heckeTorsion J 𝔪 ≠ ⊥) :
    ∃ ι : (Fin 2 → HeckeAlg ⧸ 𝔪) →ₗ[HeckeAlg ⧸ 𝔪] heckeTorsion J 𝔪, Function.Injective ι ∧
      ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (v : Fin 2 → HeckeAlg ⧸ 𝔪),
        ι ((ρ σ).mulVec v) = mTorsionGaloisRep J 𝔪 σ (ι v) := by sorry
