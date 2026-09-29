-- Prove2me | Theorems.Thm_ModularCurve_exists_submodule_finrank_span_toricMonodromyPart_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero
-- name    : ModularCurve.exists_submodule_finrank_span_toricMonodromyPart_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/e234150b-521b-5722-812b-429d4689a326
-- title:
--   Interchange inequality for toric monodromy at q and q'
-- statement:
--   Let $p$ be a prime, let $N,q,q'$ be naturals with $q$ and $q'$ prime, $q'\ge 5$, $q\nmid N$, $q'\nmid N$, $q'\neq q$, $q\neq p$, $q'\neq p$, $p\neq 2$, $N$ squarefree, and let $D$ be a nonzero natural with $6Nqq'\mid D$. Let $\mathfrak m$ be a maximal ideal of the Hecke algebra $\mathbb T=\mathbb Z[X_\ell:\ell\text{ prime}]$ with $p\in\mathfrak m$ and $X_{q'}^2-1\in\mathfrak m$, not eventually Eisenstein (no finite set $S$ of primes with $X_\ell-(\ell+1)\in\mathfrak m$ for all $\ell\notin S$), and assume $p\nmid q'-1$ and $p\mid q-1$ in $\mathbb Z$. Let $A_1,A_2$ be valuation subrings of $\overline{\mathbb Q}$ with $q'$, resp. $q$, a nonunit, with associated inertia subgroups of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$. The Jacobians $\mathrm{JZero}$ of levels $Nq'$ and $Nq'q$ carry the $\mathbb T$-action `heckeModuleBar`, and $\mathfrak m$-torsion means $\mathbb T$-torsion by the set $\mathfrak m$. Assume: the inertia subgroup of $A_2$ fixes the $\mathfrak m$-torsion of $\mathrm{JZero}(Nq'q)$ pointwise; and there are a finite field $F$, a ring map $\iota:F\to\mathbb T/\mathfrak m$, an $n$, a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $2\times 2$ matrices over $F$, and a $\mathbb T/\mathfrak m$-linear isomorphism $e$ from the $\mathfrak m$-torsion onto $(\mathrm{Fin}\,n\to F^2\otimes)$, i.e. $\mathrm{Fin}\,n\to\mathrm{Fin}\,2\to\mathbb T/\mathfrak m$, transporting the Galois action to $n$ copies of $\rho$ pushed along $\iota$, such that for some finite set $S\subseteq\mathbb N$ whose complement consists of primes not dividing $Dp$ one has, for every prime $\ell\notin S$, every valuation subring over $\ell$ and every Frobenius $\sigma$ at $\ell$, $X_\ell\equiv\mathrm{tr}$ and $\ell\equiv\det$ of $(\rho\sigma)$ modulo $\mathfrak m$; $\rho$ is odd (some $c$ with $\rho c^2=1$, $\det\rho c=-1$); $\rho$ is trivial on the subgroup fixing some finite extension of $\mathbb Q$; and no nonzero vector of $F^2$ spans a $\rho$-stable line. Then, provided there is no finite set $S$ of primes all dividing $Nqq'$ for which $\mathrm{JZero}(Nq')$ has a nonzero element killed by every integer in $\mathfrak m$ and by every $X_\ell-b$ ($\ell\notin S$ prime, $b\in\mathbb Z$) lying in $\mathfrak m$, there exists a $\mathbb T/\mathfrak m$-submodule $Z'$ of the $\mathfrak m$-torsion of $\mathrm{JZero}(Nq'q)$ all of whose elements lie in the toric monodromy part at $q'$ for the inertia of $A_1$ (the span of $\sigma\cdot x-x$ with $\sigma$ inertial and $x$ killed by some positive integer coprime to $q'$) and in the kernels of both degeneracy pushforwards $\mathrm{JZero}(Nq'q)\to\mathrm{JZero}(Nq')$, and such that the $\mathbb T/\mathfrak m$-dimension of the span of the preimage in the $\mathfrak m$-torsion of the toric monodromy part at $q$ for the inertia of $A_2$ is at most $\dim_{\mathbb T/\mathfrak m}Z'$.
--
--   This is a step in Ribet-style level lowering at the prime $q$: it compares the $q$-toric monodromy part of the $\mathfrak m$-torsion of the Jacobian of level $Nq'q$ with a subspace supported in the $q'$-toric part and in the kernel of the two $q$-degeneracy maps. It is used in the cardinality bound for the toric torsion that follows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_submodule_finrank_span_toricMonodromyPart_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem
  ModularCurve.exists_submodule_finrank_span_toricMonodromyPart_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hq'5 : 5 ≤ q') (hqN : ¬ q ∣ N) (hqq' : q' ≠ q) (D : ℕ) [NeZero D] (hD : 6 * N * q * q' ∣ D) (hqp : q ≠ p)
    (hq'p : q' ≠ p)
    (hp2 : p ≠ 2) (hq'N : ¬ q' ∣ N) [NeZero (N * q')] [NeZero q] (hN : Squarefree N)
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪) (heis : ¬ IsEventuallyEisenstein 𝔪)
    (hnew : heckeGen ⟨q', hq'⟩ ^ 2 - 1 ∈ 𝔪)
    (hq'1 : ¬ (p : ℤ) ∣ (q' : ℤ) - 1)
    (hq1 : (p : ℤ) ∣ (q : ℤ) - 1)
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)
    (hunrJ : letI := heckeModuleBar (N * q' * q)
      ∀ σ ∈ A₂.inertiaSubgroupIn ℚ,
        ∀ x ∈ heckeTorsion (JZero (N * q' * q)) 𝔪, σ • x = x)
    (hblr : letI := heckeModuleBar (N * q' * q)
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (ι : F →+* HeckeAlg ⧸ 𝔪) (n : ℕ)
        (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
        (e : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪) ≃ₗ[HeckeAlg ⧸ 𝔪] (Fin n → Fin 2 → HeckeAlg ⧸ 𝔪)),
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪)),
            σ • (w : JZero (N * q' * q)) = ↑(e.symm fun i => ((ρ σ).map ι).mulVec (e w i))) ∧
          (∃ S : Finset ℕ, (∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ D * p) ∧
            ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
              A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
                Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = ((ρ σ).map ι).trace ∧
                  Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = ((ρ σ).map ι).det) ∧
          (∃ c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ c * ρ c = 1 ∧ (ρ c).det = -1) ∧
          GaloisFactorsThroughFiniteLevel ρ ∧
          ∀ v : Fin 2 → F, v ≠ 0 →
            ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ c : F, (ρ σ).mulVec v ≠ c • v) :
    letI := heckeModuleBar (N * q')
    letI := heckeModuleBar (N * q' * q)
    (¬ ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q * q') ∧
        HasLowerLevelTorsion S 𝔪 (JZero (N * q'))) →
      ∃ Z' : Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (JZero (N * q' * q)) 𝔪),
        (∀ z ∈ Z', ((z : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪)) : JZero (N * q' * q)) ∈
              toricMonodromyPart (J := JZero (N * q' * q)) q' (A₁.inertiaSubgroupIn ℚ) ∧
            degeneracyPushforwardPair (N * q') q 0
              ((z : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪)) : JZero (N * q' * q)) = 0 ∧
            degeneracyPushforwardPair (N * q') q 1
              ((z : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪)) : JZero (N * q' * q)) = 0) ∧
        Module.finrank (HeckeAlg ⧸ 𝔪)
            ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
              ((Subtype.val : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪) → JZero (N * q' * q)) ⁻¹'
                (toricMonodromyPart (J := JZero (N * q' * q)) q (A₂.inertiaSubgroupIn ℚ) : Set (JZero (N * q' * q)))))
          ≤ Module.finrank (HeckeAlg ⧸ 𝔪) ↥Z' := by sorry
