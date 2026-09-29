-- Prove2me | Theorems.Thm_HeckeEis_exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom
-- name    : HeckeEis.exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/069b151b-c5b2-5602-a8da-45ddda320bd4
-- title:
--   Partial Hecke eigensystems on H¹(Γ₀(N),Symⁿ) extend to full ones
-- statement:
--   Fix a prime $p$, an integer $N \ne 0$, a set $S_0 \subseteq \mathbb{N}$, an integer $n$, a field $\kappa$ of characteristic $p$, a ring homomorphism $\varphi$ from the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ (the algebraic integers) to $\kappa$, and a function $\mathrm{lam} \colon \mathbb{N} \to \kappa$. Let $\rho$ be the representation of $\Gamma_0(N)$ on the space `BinaryForm` $\kappa$ $n$ of degree-$n$ homogeneous polynomials in $\kappa[X_0,X_1]$ obtained by restricting `binaryFormRepSL`, where $g \in \mathrm{SL}_2(\mathbb{Z})$ acts by the substitution $X_j \mapsto \sum_i g_{ij} X_i$, and for each $\ell$ let $a_\ell =$ `binaryFormAlphaAdj` $\kappa$ $n$ $\ell$ be the coefficient map given by substituting $\mathrm{diag}(\ell,1)$, i.e. $X_0 \mapsto \ell X_0$, $X_1 \mapsto X_1$. Write $H =$ `coeffH1` $\rho$, the quotient of the module of inhomogeneous $1$-cocycles `coeffCocycles` $\rho$ by the coboundaries. The hypothesis is that $\mathrm{lam}$ is an eigensystem on $H$ away from $S_0$: there is a nonzero $x \in H$ such that for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$ there is a $\kappa$-linear endomorphism $T$ of $H$ which is a Hecke operator at $\ell$ in the sense of `IsCoeffHeckeOnH1` (for every cocycle $z$ the function `coeffHeckeFun` $N$ $\ell$ $\rho$ $a_\ell$ $z$ is again a cocycle and $T$ sends the class of $z$ to its class) and $Tx = \mathrm{lam}(\ell)\,x$. The conclusion asserts the existence of $\mathrm{mu} \colon \mathbb{N} \to \kappa$ which is an eigensystem on $H$ in the same sense with $S_0$ replaced by $\emptyset$, so with an eigenclass, possibly different from $x$, at every prime $\ell \nmid N$, and which satisfies $\mathrm{mu}(\ell) = \mathrm{lam}(\ell)$ for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$.
--
--   This is the step passing from a system of Hecke eigenvalues defined only outside an arbitrary exceptional set $S_0$ of primes to a full system of eigenvalues at all primes not dividing the level, agreeing with the original one outside $S_0$. It is used by [`GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom`](thm.html#GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom) to attach Galois representations to eigenclasses in $H^1(\Gamma_0(N),\mathrm{Sym}^n(\kappa^2))$ given only away from $S_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ) (n : ℕ)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    ∃ mu : ℕ → κ,
      HeckeEis.IsEigensystemH1 N
        ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
        (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) ∅ mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → mu ℓ = lam ℓ := by sorry
