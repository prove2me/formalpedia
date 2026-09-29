-- Prove2me | Theorems.Thm_GaloisRep_exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom
-- name    : GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/18ed6f95-3e21-583a-8ca6-65d6d4719bf8
-- title:
--   Residual Galois representation attached to an H¹ Hecke eigensystem
-- statement:
--   Fix a prime $p$, an integer $N \ge 1$, a set $S_0 \subseteq \mathbb{N}$, an integer $n \ge 0$, a field $\kappa$ of characteristic $p$, a ring homomorphism $\varphi$ from the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ into $\kappa$, and a function $\lambda \colon \mathbb{N} \to \kappa$. Let $\mathrm{SL}_2(\mathbb{Z})$ act on the space of degree-$n$ homogeneous binary forms over $\kappa$ by the substitution $X_j \mapsto \sum_i M_{ij} X_i$ (`binaryFormRepSL`), restricted along the inclusion $\Gamma_0(N) \hookrightarrow \mathrm{SL}_2(\mathbb{Z})$, and let the coefficient map at $\ell$ be substitution by $\mathrm{diag}(\ell,1)$, i.e. $P(X_0,X_1) \mapsto P(\ell X_0, X_1)$. The hypothesis is that $\lambda$ is an eigensystem away from $S_0$ in the first cohomology of $\Gamma_0(N)$ with these coefficients: there is a nonzero class $x$ in inhomogeneous $1$-cocycles modulo coboundaries such that for every prime $\ell \nmid N$ with $\ell \notin S_0$ some $\kappa$-linear endomorphism $T$ of that cohomology is induced by the Hecke cocycle operator at $\ell$ with the above coefficient map, and $T x = \lambda(\ell)\, x$. The conclusion produces a group homomorphism $\rho \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\kappa)$, where $\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`, such that: (i) $\rho$ is trivial on all $\sigma$ fixing some finite-dimensional intermediate field $L/\mathbb{Q}$ pointwise; (ii) for every prime $\ell \nmid N$ with $\ell \notin S_0$ and $\ell \ne p$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acting as $x \mapsto x^{\ell}$ on the residue field of $A$, one has $\mathrm{tr}\,\rho(\sigma) = \lambda(\ell)$; (iii) under the same hypotheses but without requiring $\ell \notin S_0$, $\det \rho(\sigma) = \ell^{\,n+1}$ in $\kappa$; (iv) for every prime $\ell \nmid N$, $\ell \ne p$, every such $A$ over $\ell$, and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$, $\rho(\sigma) = 1$.
--
--   This is Deligne's construction of the Galois representation attached to a system of Hecke eigenvalues of weight $n+2$, in residual form and read in the group cohomology of $\Gamma_0(N)$ with $\mathrm{Sym}^n$ coefficients: only traces and determinants of Frobenius elements, unramifiedness outside $Np$, and factorisation through a finite extension of $\mathbb{Q}$ are asserted, so no semisimplicity or irreducibility is claimed. It feeds the passage from eigensystems to Galois characters used in [`GaloisRep.exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le`](thm.html#GaloisRep.exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ) (n : ℕ)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val = lam ℓ) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.det (ρ σ).val = (ℓ : κ) ^ (n + 1)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) := by sorry
