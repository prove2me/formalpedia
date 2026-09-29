-- Prove2me | Theorems.Thm_ModularCurve_cayleyHamilton_forall_of_frobeniusQuadratic_of_dense
-- name    : ModularCurve.cayleyHamilton_forall_of_frobeniusQuadratic_of_dense
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/725146e7-38e2-530f-8551-d4b52fb2edc0
-- title:
--   Cayley–Hamilton identity for all σ on J[𝔪]
-- statement:
--   Let $J$ be an additive commutative group carrying a module structure over the Hecke algebra $\mathbb T=$ [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) $=\mathbb Z[X_\ell:\ell\in\mathrm{Primes}]$ and a distributive action of $G=\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)=(\mathrm{AlgebraicClosure}\,\mathbb Q\simeq_{\mathbb Q}\mathrm{AlgebraicClosure}\,\mathbb Q)$ commuting with the $\mathbb T$-action. Fix natural numbers $N,p$, an ideal $\mathfrak m\subseteq\mathbb T$ with $p\in\mathfrak m$, and a monoid homomorphism $\rho:G\to M_2(\mathbb T/\mathfrak m)$. Assume: (i) `FrobeniusQuadratic` for $N,p,J$ over $\mathbb Q\subseteq\overline{\mathbb Q}$, i.e. for every prime $\ell\nmid Np$, every valuation subring $A\subseteq\overline{\mathbb Q}$ with $\ell$ a nonunit of $A$, every $\sigma$ lying in the decomposition subgroup of $A$ and inducing $x\mapsto x^{\ell}$ on the residue field of $A$, and every $x\in J$ killed by some power of $p$, one has $\sigma^2x-X_\ell\cdot(\sigma x)+\ell x=0$; (ii) a finite set $S$ of naturals such that every prime outside $S$ fails to divide $Np$; (iii) for every prime $\ell\notin S$, every such $A$ and every Frobenius $\sigma$ at $\ell$ for $A$, $X_\ell\equiv\operatorname{tr}\rho(\sigma)$ and $\ell\equiv\det\rho(\sigma)$ in $\mathbb T/\mathfrak m$; (iv) [`FrobeniusPowerDense`](def/GaloisRep_FrobeniusPowerDense.html#L7) for $S$ and the subgroup $\ker\rho\cap\mathrm{Fix}(J[\mathfrak m])$, i.e. every $\sigma\in G$ is, modulo that subgroup, a conjugate of a power $\tau^n$ of a Frobenius $\tau$ at some prime $\ell\notin S$. Then for every $\sigma\in G$, every $x$ in $J[\mathfrak m]=\mathrm{torsionBySet}_{\mathbb T}(J,\mathfrak m)$ and all $t,d\in\mathbb T$ reducing to $\operatorname{tr}\rho(\sigma)$ and $\det\rho(\sigma)$ modulo $\mathfrak m$, $\ \sigma^2x-t\cdot(\sigma x)+d\,x=0$.
--
--   This globalises the Eichler–Shimura congruence relation: the quadratic relation, known at Frobenius elements outside $S$ from the action on $p$-power torsion, is propagated to all of $G_{\mathbb Q}$ on $J[\mathfrak m]$, where the choice of lifts $t,d$ of trace and determinant is immaterial. It supplies the Cayley–Hamilton input for the Boston–Lenstra–Ribet block decomposition ([`ModularCurve.exists_blrBlock_of_frobeniusQuadratic_of_dense`](thm.html#ModularCurve.exists_blrBlock_of_frobeniusQuadratic_of_dense)) and for the corresponding statement at an Eisenstein maximal ideal, the density step being [`Representation.cayleyHamilton_of_frobeniusPowerDense`](thm.html#Representation.cayleyHamilton_of_frobeniusPowerDense).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_cayleyHamilton_forall_of_frobeniusQuadratic_of_dense.lean

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.cayleyHamilton_forall_of_frobeniusQuadratic_of_dense {J : Type*} [AddCommGroup J]
    [Module ModularCurve.HeckeAlg J] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal ModularCurve.HeckeAlg) (hp : ((p : ℕ) : ModularCurve.HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (ModularCurve.HeckeAlg ⧸ 𝔪))
    (hES : ModularCurve.FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧ Ideal.Quotient.mk 𝔪 ((ℓ : ModularCurve.HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (ModularCurve.heckeTorsion J 𝔪 : Set J))) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : J), x ∈ ModularCurve.heckeTorsion J 𝔪 →
      ∀ (t d : ModularCurve.HeckeAlg), Ideal.Quotient.mk 𝔪 t = (ρ σ).trace → Ideal.Quotient.mk 𝔪 d = (ρ σ).det →
        σ • σ • x - t • (σ • x) + d • x = 0 := by sorry
