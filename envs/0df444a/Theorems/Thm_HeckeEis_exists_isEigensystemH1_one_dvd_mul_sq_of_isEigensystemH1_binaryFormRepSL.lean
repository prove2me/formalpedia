-- Prove2me | Theorems.Thm_HeckeEis_exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL
-- name    : HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/518f3381-c999-530e-a253-ecff5ca8a998
-- title:
--   Ash–Stevens reduction to weight two, level dividing Np²
-- statement:
--   Let $p$ be a prime, $N\ge 1$ an integer, $S_0$ a set of natural numbers, $n$ a natural number and $\kappa$ a field of characteristic $p$, and let $\mathrm{lam}\colon\mathbb{N}\to\kappa$ be a function. Consider the space `BinaryForm κ n` of homogeneous polynomials of degree $n$ in $\kappa[X_0,X_1]$, with $\Gamma_0(N)\subseteq \mathrm{SL}(2,\mathbb{Z})$ acting through `binaryFormRepSL` by the substitution $X_j\mapsto \sum_i M_{ij}X_i$ attached to the matrix $M$, and for a prime $\ell$ the coefficient endomorphism `binaryFormAlphaAdj κ n ℓ` given by substituting $\mathrm{diag}(\ell,1)$, i.e. $P(X_0,X_1)\mapsto P(\ell X_0,X_1)$. The hypothesis is that $\mathrm{lam}$ is an eigensystem in the sense of `IsEigensystemH1` for this datum away from $S_0$: in the cohomology `coeffH1` (cocycles modulo coboundaries) there is a nonzero class $x$ such that for every prime $\ell$ with $\ell\nmid N$ and $\ell\notin S_0$ there is a $\kappa$-linear endomorphism $T$ of `coeffH1` which is induced on classes by the cochain-level Hecke operator `coeffHeckeFun` at $\ell$ with coefficient map `binaryFormAlphaAdj κ n ℓ`, and $Tx=\mathrm{lam}(\ell)\,x$. The conclusion asserts the existence of an integer $M$ dividing $Np^2$ and a function $\mathrm{mu}\colon\mathbb{N}\to\kappa$ which is an eigensystem in the same sense for the trivial one-dimensional representation of $\Gamma_0(M)$ on $\kappa$, with all coefficient maps the identity, away from $S_0\cup\{p\}$, and such that $\mathrm{lam}(\ell)=\ell^{\,n/2}\,\mathrm{mu}(\ell)$ (natural-number division, so the exponent is $\lfloor n/2\rfloor$) for every prime $\ell$ with $\ell\nmid N$, $\ell\neq p$ and $\ell\notin S_0$.
--
--   This is the reduction, due to Ash and Stevens and, in the language of modular forms modulo $p$, to Serre, of mod-$p$ Hecke eigensystems in weight $n+2$ and level $\Gamma_0(N)$ to weight two, trivial coefficients and level dividing $Np^2$, at the cost of the twist by the $\lfloor n/2\rfloor$-th power of $\ell$. It is used to attach Galois representations to eigensystems in $H^1(\Gamma_0(N),\mathrm{Sym}^n)$ via the weight-two case, and is invoked by [`GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom`](thm.html#GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom); the proof cites the level-raising step at an auxiliary prime, the passage to a nebentypus representation at $p$, and the weight-two statement for $\Gamma_0$ with trivial coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ) (n : ℕ)
    (κ : Type) [Field κ] [CharP κ p] (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    ∃ (M : ℕ) (mu : ℕ → κ), M ∣ N * p ^ 2 ∧
      HeckeEis.IsEigensystemH1 M (1 : Representation κ (CongruenceSubgroup.Gamma0 M) κ)
        (fun _ => LinearMap.id) (insert p S₀) mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ℓ ∉ S₀ → lam ℓ = (ℓ : κ) ^ (n / 2) * mu ℓ := by sorry
