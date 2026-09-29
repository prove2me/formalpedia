-- Prove2me | Theorems.Thm_ModularCurve_exists_blrDecomposition_heckeTorsion_of_span_eq_top_of_frobeniusQuadratic_of_dense
-- name    : ModularCurve.exists_blrDecomposition_heckeTorsion_of_span_eq_top_of_frobeniusQuadratic_of_dense
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/b55df979-f70f-59f4-8307-54ffcdac11f2
-- title:
--   J[𝔪] is a direct sum of copies of ρ
-- statement:
--   Let $\mathbb T =$ `HeckeAlg` be the polynomial ring $\mathbb Z[X_\ell : \ell \text{ prime}]$, whose generator at $\ell$ is written $\mathrm{heckeGen}\,\ell$, and let $J$ be an abelian group carrying a $\mathbb T$-module structure together with an action of $G = \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (the automorphism group of `AlgebraicClosure ℚ` over $\mathbb Q$) commuting with the $\mathbb T$-action. Fix natural numbers $N, p$, a maximal ideal $\mathfrak m \subset \mathbb T$ with $p \in \mathfrak m$, and a monoid homomorphism $\rho : G \to M_2(k)$, $k = \mathbb T/\mathfrak m$, subject to: $2 \neq 0$ in $k$; the $k$-span of $\{\rho(g) : g \in G\}$ is all of $M_2(k)$; the predicate `FrobeniusQuadratic` for $N, p, J$ over $\mathbb Q \subset \overline{\mathbb Q}$, i.e. for every prime $\ell \nmid Np$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, every $\sigma$ in the decomposition subgroup of $A$ acting on the residue field of $A$ by $x \mapsto x^\ell$, and every $x \in J$ killed by some power of $p$, one has $\sigma^2 x - X_\ell \cdot (\sigma x) + \ell x = 0$; a finite set $S$ of naturals containing all primes dividing $Np$ (stated as: every prime outside $S$ fails to divide $Np$); and, for every prime $\ell \notin S$, every such $A$ and every such Frobenius $\sigma$ at $\ell$, the congruences $X_\ell \equiv \mathrm{tr}\,\rho(\sigma)$ and $\ell \equiv \det \rho(\sigma)$ in $k$. Assume further [`FrobeniusPowerDense`](def/GaloisRep_FrobeniusPowerDense.html#L7) for $S$ and the subgroup $\ker \rho \cap \mathrm{Fix}(J[\mathfrak m])$, the pointwise stabiliser of $J[\mathfrak m] =$ `heckeTorsion J 𝔪` $= \{x : \mathfrak m x = 0\}$: every $\sigma \in G$ satisfies $g\tau^n g^{-1}\sigma^{-1} \in \ker\rho \cap \mathrm{Fix}(J[\mathfrak m])$ for some prime $\ell \notin S$, some valuation subring $A$ in which $\ell$ is a non-unit, some Frobenius $\tau$ at $\ell$ for $A$, some $g \in G$ and some $n \in \mathbb N$. Finally assume $J[\mathfrak m]$ is finite. Then there are $n \in \mathbb N$ and a $k$-linear isomorphism $e : J[\mathfrak m] \to (k^2)^{n}$ such that for all $\sigma \in G$, $w \in J[\mathfrak m]$ and $i < n$, the $i$-th component of $e(\sigma w)$ equals $\rho(\sigma)$ applied to the $i$-th component of $e(w)$; here $\sigma w$ is the action through `mTorsionGaloisRep`.
--
--   This is the Boston–Lenstra–Ribet multiplicity statement in the setting of Hecke modules: under the stated conditions the $\mathfrak m$-torsion of $J$ is $G$-equivariantly a direct sum of copies of the two-dimensional representation $\rho$. It is the form in which the structure of $J[\mathfrak m]$ enters the level-lowering arguments, and is cited for instance in the analysis of torsion data at two places and in the construction of stable lines for $\rho$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_blrDecomposition_heckeTorsion_of_span_eq_top_of_frobeniusQuadratic_of_dense.lean

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_blrDecomposition_heckeTorsion_of_span_eq_top_of_frobeniusQuadratic_of_dense {J : Type} [AddCommGroup J] [Module HeckeAlg J]
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
    (hfin : Finite (heckeTorsion J 𝔪)) :
    ∃ (n : ℕ) (e : heckeTorsion J 𝔪 ≃ₗ[HeckeAlg ⧸ 𝔪] (Fin n → (Fin 2 → HeckeAlg ⧸ 𝔪))),
      ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (w : heckeTorsion J 𝔪) (i : Fin n),
        e (mTorsionGaloisRep J 𝔪 σ w) i = (ρ σ).mulVec (e w i) := by sorry
