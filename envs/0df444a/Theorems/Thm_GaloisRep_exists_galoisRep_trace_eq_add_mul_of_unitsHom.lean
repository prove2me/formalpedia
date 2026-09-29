-- Prove2me | Theorems.Thm_GaloisRep_exists_galoisRep_trace_eq_add_mul_of_unitsHom
-- name    : GaloisRep.exists_galoisRep_trace_eq_add_mul_of_unitsHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/463d28d1-b713-55e3-99ce-33742295c5cf
-- title:
--   Reducible mod p representation with prescribed Frobenius traces
-- statement:
--   Let $p$ be a prime, $N$ a nonzero natural number, $\kappa$ a field of characteristic $p$, and let $\psi_1,\psi_2 \colon (\mathbb{Z}/N\mathbb{Z})^\times \to \kappa^\times$ be group homomorphisms. Then there exists a group homomorphism $\rho \colon \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}}) \to \mathrm{GL}_2(\kappa)$, where $\overline{\mathbb{Q}}$ is the chosen algebraic closure of $\mathbb{Q}$, with the following three properties. First, $\rho$ factors through a finite level: there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that $\rho\sigma = 1$ for every $\sigma$ fixing $L$ pointwise. Second, for every prime $\ell$ with $\ell \nmid N$ and $\ell \neq p$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma$ in the decomposition subgroup of $A$ over $\mathbb{Q}$ acting on the residue field of $A$ by $x \mapsto x^{\ell}$, one has $\operatorname{tr}\rho(\sigma) = \psi_1(\ell) + \ell\,\psi_2(\ell)$ and $\det\rho(\sigma) = \psi_1(\ell)\,\psi_2(\ell)\,\ell$ in $\kappa$, with $\ell$ read as the unit of $\mathbb{Z}/N\mathbb{Z}$ determined by its coprimality to $N$. Third, for such $\ell$ and $A$, $\rho\sigma = 1$ for every $\sigma$ in the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $A$ over $\mathbb{Q}$.
--
--   This produces the reducible two-dimensional representation $\psi_1 \oplus \varepsilon\psi_2$, with $\varepsilon$ the mod $p$ cyclotomic character and the $\psi_i$ read through the mod $N$ cyclotomic character, together with its Frobenius data and its unramifiedness away from $Np$. It is used to realise Eisenstein systems of Hecke eigenvalues by Galois representations, in [`GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom`](thm.html#GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_galoisRep_trace_eq_add_mul_of_unitsHom.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem GaloisRep.exists_galoisRep_trace_eq_add_mul_of_unitsHom
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (κ : Type) [Field κ] [CharP κ p]
    (ψ₁ ψ₂ : (ZMod N)ˣ →* κˣ) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val =
                (ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) +
                  (ℓ : κ) * (ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) ∧
            Matrix.det (ρ σ).val =
                (ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) *
                  (ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) * (ℓ : κ)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) := by sorry
