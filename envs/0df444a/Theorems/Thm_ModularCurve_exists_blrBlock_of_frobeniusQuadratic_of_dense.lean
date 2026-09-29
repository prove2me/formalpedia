-- Prove2me | Theorems.Thm_ModularCurve_exists_blrBlock_of_frobeniusQuadratic_of_dense
-- name    : ModularCurve.exists_blrBlock_of_frobeniusQuadratic_of_dense
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/00819823-9906-5a86-bf48-86b077c846a0
-- title:
--   Boston–Lenstra–Ribet embedding of ρ into J[𝔪]
-- statement:
--   Let $\mathbb T =$ [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) be the polynomial ring $\mathbb Z[X_\ell : \ell \text{ prime}]$, whose variable at $\ell$ is written $T_\ell =$ `heckeGen`, and let $J$ be an abelian group carrying a $\mathbb T$-module structure and a distributive action of $G = \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (realised as $\overline{\mathbb Q}$-algebra automorphisms of `AlgebraicClosure ℚ`) commuting with the $\mathbb T$-action. Fix natural numbers $N, p$, a maximal ideal $\mathfrak m \subset \mathbb T$ whose image contains $p$, and a monoid homomorphism $\rho : G \to \mathrm{M}_2(\mathbb T/\mathfrak m)$ such that every subspace $W \subseteq (\mathbb T/\mathfrak m)^2$ stable under all $\rho(g)$ (acting by `mulVec`) is $\bot$ or $\top$, and such that for some $c \in G$ one has $\rho(c)^2 = 1$ and $\det \rho(c) = -1$; assume $2 \neq 0$ in $\mathbb T/\mathfrak m$. Assume the quadratic Frobenius relation `FrobeniusQuadratic`: for every prime $\ell \nmid Np$, every valuation subring $A \subseteq \overline{\mathbb Q}$ with $\ell$ a non-unit of $A$, every $\sigma$ lying in the decomposition subgroup of $A$ and acting on the residue field of $A$ by $x \mapsto x^\ell$, and every $x \in J$ killed by some power of $p$, $\sigma\cdot\sigma\cdot x - T_\ell\cdot(\sigma\cdot x) + \ell\, x = 0$. Let $S$ be a finite set of naturals such that no prime outside $S$ divides $Np$, and assume that for every prime $\ell \notin S$ and every such $A$ and Frobenius $\sigma$ at $\ell$, the images in $\mathbb T/\mathfrak m$ of $T_\ell$ and of $\ell$ equal $\operatorname{tr}\rho(\sigma)$ and $\det\rho(\sigma)$. Assume further [`FrobeniusPowerDense`](def/GaloisRep_FrobeniusPowerDense.html#L7) for $S$ and the subgroup $H = \ker\rho \cap \{\text{elements of } G \text{ fixing } J[\mathfrak m] \text{ pointwise}\}$, i.e. every $\sigma \in G$ satisfies $g\tau^n g^{-1}\sigma^{-1} \in H$ for some prime $\ell \notin S$, some valuation subring over $\ell$, some Frobenius $\tau$ at $\ell$, some $g \in G$ and some $n \in \mathbb N$. Finally assume $J[\mathfrak m] =$ `heckeTorsion J 𝔪`, the submodule of elements annihilated by $\mathfrak m$, is non-zero. Then there is an injective additive homomorphism $\iota : (\mathbb T/\mathfrak m)^2 \to J$ with $\iota(\rho(\sigma)v) = \sigma \cdot \iota(v)$ for all $\sigma \in G$ and all $v$, whose image lies in $J[\mathfrak m]$.
--
--   This is the Boston–Lenstra–Ribet theorem in the form needed for level lowering: an irreducible odd two-dimensional residual representation attached to $\mathfrak m$ away from $S$, whose Cayley–Hamilton relation is witnessed by the Eichler–Shimura relation on $p$-power torsion, embeds Galois-equivariantly into $J[\mathfrak m]$ once the latter is non-zero. It is invoked by [`ModularCurve.exists_torsionEmbedding_of_congruences`](thm.html#ModularCurve.exists_torsionEmbedding_of_congruences), in the construction of the descent data underlying Mazur's principle, with $J$ the points of a Jacobian $J_0(Nq)$; the Cayley–Hamilton input is supplied by [`ModularCurve.cayleyHamilton_forall_of_frobeniusQuadratic_of_dense`](thm.html#ModularCurve.cayleyHamilton_forall_of_frobeniusQuadratic_of_dense) and the linear-algebraic core by [`BostonLenstraRibet.exists_embedding_of_irreducible_of_odd`](thm.html#BostonLenstraRibet.exists_embedding_of_irreducible_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_blrBlock_of_frobeniusQuadratic_of_dense.lean

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_blrBlock_of_frobeniusQuadratic_of_dense {J : Type*} [AddCommGroup J]
    [Module ModularCurve.HeckeAlg J] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal ModularCurve.HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : ((p : ℕ) : ModularCurve.HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ModularCurve.HeckeAlg ⧸ 𝔪))
    (hirr : ∀ (W : Submodule (ModularCurve.HeckeAlg ⧸ 𝔪) (Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪)),
      (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hc2 : ρ c * ρ c = 1) (hcdet : (ρ c).det = -1)
    (h2 : (2 : ModularCurve.HeckeAlg ⧸ 𝔪) ≠ 0)
    (hES : ModularCurve.FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧ Ideal.Quotient.mk 𝔪 ((ℓ : ModularCurve.HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ModularCurve.heckeTorsion J 𝔪 : Set J)))
    (hne : ModularCurve.heckeTorsion J 𝔪 ≠ ⊥) :
    ∃ ι : (Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪) →+ J, Function.Injective ι ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪), ι ((ρ σ).mulVec v) = σ • ι v) ∧
      ∀ (v : Fin 2 → ModularCurve.HeckeAlg ⧸ 𝔪), ι v ∈ ModularCurve.heckeTorsion J 𝔪 := by sorry
