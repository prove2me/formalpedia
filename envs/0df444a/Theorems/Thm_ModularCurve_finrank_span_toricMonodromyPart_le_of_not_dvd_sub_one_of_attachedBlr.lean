-- Prove2me | Theorems.Thm_ModularCurve_finrank_span_toricMonodromyPart_le_of_not_dvd_sub_one_of_attachedBlr
-- name    : ModularCurve.finrank_span_toricMonodromyPart_le_of_not_dvd_sub_one_of_attachedBlr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/4ca22528-2151-583d-975a-51762b292c10
-- title:
--   Toric part of the 𝔪-torsion has rank at most n
-- statement:
--   Let $p$ be a prime, let $N,q,q'$ be natural numbers with $q$ and $q'$ prime, $q'\neq q$, $q'\neq p$ and $q'\nmid N$ (with $N q'$ and $q$ non-zero). Write $\mathbb T$ for `HeckeAlg`, the polynomial ring $\mathbb Z[X_\ell:\ell\text{ prime}]$ whose generator at $\ell$ is `heckeGen`, and let $\mathfrak m\subset\mathbb T$ be a maximal ideal with $p\in\mathfrak m$ and $X_{q'}^2-1\in\mathfrak m$, and assume $p\nmid q'-1$ in $\mathbb Z$. Let $A_1$ be a valuation subring of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` with $q'$ a non-unit of $A_1$, let $F$ be a finite field, $\iota:F\to\mathbb T/\mathfrak m$ a ring homomorphism, $n\in\mathbb N$, and $\rho:\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to M_2(F)$ a monoid homomorphism. Equip $J=$ `JZero (N * q' * q)`, the degree-zero divisor class group of the base-changed modular function field of level $Nq'q$, with the Hecke module structure `heckeModuleBar`, and let $J[\mathfrak m]$ be the $\mathfrak m$-torsion submodule. Assume given a $\mathbb T/\mathfrak m$-linear isomorphism $e:J[\mathfrak m]\to (\mathrm{Fin}\,n\to \mathrm{Fin}\,2\to\mathbb T/\mathfrak m)$ such that for all $\sigma$ and all $w\in J[\mathfrak m]$ one has $\sigma\cdot w=e^{-1}\bigl(i\mapsto (\iota\circ\rho(\sigma))\,(e(w)(i))\bigr)$, i.e. $J[\mathfrak m]$ is $n$ copies of $\rho\otimes_\iota \mathbb T/\mathfrak m$; assume further that there is a finite set $S$ of naturals containing every prime dividing $Nq'qp$ such that for every prime $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ in which $\ell$ is a non-unit, and every $\sigma$ lying in the decomposition subgroup of $A$ and acting as $x\mapsto x^{\ell}$ on the residue field, the class of $X_\ell$ in $\mathbb T/\mathfrak m$ is the trace of $\iota\circ\rho(\sigma)$ and the class of $\ell$ is its determinant; and assume $\rho$ is trivial on the subgroup fixing some finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$. Then the $\mathbb T/\mathfrak m$-rank of the span, inside $J[\mathfrak m]$, of those elements whose image in $J$ lies in `toricMonodromyPart` $q'$ for the inertia subgroup of $A_1$ pushed into $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ — the $\mathbb T$-submodule of $J$ spanned by the elements $\sigma\cdot x-x$ with $\sigma$ in that inertia subgroup and $x$ killed by some $m>0$ coprime to $q'$ — is at most $n$.
--
--   This is the bound at the auxiliary prime $q'$ in Ribet's interchange (level-raising/level-lowering) argument: when $T_{q'}^2\equiv 1$ and $q'\not\equiv 1 \pmod{p}$, each of the $n$ copies of $\rho$ inside $J_0(Nq'q)[\mathfrak m]$ contributes at most one line to the toric part at $q'$. It feeds the statement [`ModularCurve.exists_submodule_finrank_span_toricMonodromyPart_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero`](thm.html#ModularCurve.exists_submodule_finrank_span_toricMonodromyPart_le_of_not_exists_hasLowerLevelTorsion_of_attachedOddBlr_sqf_five_of_six_mul_dvd_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_span_toricMonodromyPart_le_of_not_dvd_sub_one_of_attachedBlr.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.finrank_span_toricMonodromyPart_le_of_not_dvd_sub_one_of_attachedBlr
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hqq' : q' ≠ q) (hq'p : q' ≠ p)
    (hq'N : ¬ q' ∣ N) [NeZero (N * q')] [NeZero q]
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪)
    (hnew : heckeGen ⟨q', hq'⟩ ^ 2 - 1 ∈ 𝔪)
    (hq'1 : ¬ (p : ℤ) ∣ (q' : ℤ) - 1)
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    (F : Type) [Field F] [Fintype F] (ι : F →+* HeckeAlg ⧸ 𝔪) (n : ℕ)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
    (e : letI := heckeModuleBar (N * q' * q)
      ↥(heckeTorsion (JZero (N * q' * q)) 𝔪) ≃ₗ[HeckeAlg ⧸ 𝔪] (Fin n → Fin 2 → HeckeAlg ⧸ 𝔪))
    (hρ : letI := heckeModuleBar (N * q' * q)
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪)),
            σ • (w : JZero (N * q' * q)) = ↑(e.symm fun i => ((ρ σ).map ι).mulVec (e w i))))
    (hatt :
      (∃ S : Finset ℕ, (∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * q' * q * p) ∧
          ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
            A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
              Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = ((ρ σ).map ι).trace ∧
                Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = ((ρ σ).map ι).det))
    (hfin : GaloisFactorsThroughFiniteLevel ρ) :
    letI := heckeModuleBar (N * q' * q)
    Module.finrank (HeckeAlg ⧸ 𝔪)
        ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
          ((Subtype.val : ↥(heckeTorsion (JZero (N * q' * q)) 𝔪) → JZero (N * q' * q)) ⁻¹'
            (toricMonodromyPart (J := JZero (N * q' * q)) q' (A₁.inertiaSubgroupIn ℚ) : Set (JZero (N * q' * q)))))
      ≤ n := by sorry
