-- Prove2me | Theorems.Thm_HeckeEis_exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1
-- name    : HeckeEis.exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/88331c7c-96c9-5a7f-9ff7-d3d430e3ec22
-- title:
--   Weight reduction to a ≤ p-1 for binary-form eigensystems
-- statement:
--   Let $p$ be a prime, $N \ge 1$, $S_0$ a set of natural numbers with $p \in S_0$, $F$ a field of characteristic $p$, $n$ a natural number and $\lambda : \mathbb{N} \to F$. Write $\mathrm{BinaryForm}\,F\,m$ for the submodule of homogeneous polynomials of degree $m$ in $F[X_0,X_1]$, on which $SL(2,\mathbb{Z})$ acts by the substitution representation `binaryFormRepSL` sending $g$ to $X_j \mapsto \sum_i g_{ij}X_i$, restricted along the inclusion of $\Gamma_0(N)$, and let `binaryFormAlphaAdj` $F\,m\,\ell$ be the substitution by $\mathrm{diag}(\ell,1)$, i.e. $P(X_0,X_1) \mapsto P(\ell X_0, X_1)$. The hypothesis is that $\lambda$ is an eigensystem in degree $n$ in the sense of `IsEigensystemH1`: there is a nonzero class $x$ in `coeffH1` of that representation (the quotient of the cocycles `coeffCocycles` by the coboundaries `coeffCoboundaries`) such that for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$ there is an $F$-linear endomorphism $T$ of `coeffH1` which is a Hecke operator at $\ell$ with coefficient map `binaryFormAlphaAdj` $F\,n\,\ell$ — for each cocycle $z$ the function `coeffHeckeFun` $N\,\ell$ applied to $z$ is again a cocycle $w$ and $T$ sends the class of $z$ to the class of $w$ — and $Tx = \lambda(\ell)\,x$. The conclusion is that there exist natural numbers $a \le p-1$ (truncated subtraction) and $j$ such that the twisted system $\ell \mapsto \ell^{\,j}\lambda(\ell)$, with $\ell$ read in $F$, is likewise an eigensystem in the same sense for the degree-$a$ binary forms, with coefficient maps `binaryFormAlphaAdj` $F\,a\,\ell$ and the same excluded set $S_0$.
--
--   This is the cohomological weight-reduction step of Ash–Stevens: an eigensystem occurring in the first cohomology of $\Gamma_0(N)$ with coefficients in binary forms of arbitrary degree $n$ occurs, after twisting by a power of $\ell$, with coefficients in binary forms of degree at most $p-1$. It rests on a $GL_2$-stable filtration of the degree-$n$ forms whose graded pieces are degree-$a$ forms with $a \le p-1$ twisted by a power of the determinant, and it is used in the reduction of mod $p$ modular forms to small weight.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1
    (p : ℕ) (hp : p.Prime) (N : ℕ) [NeZero N] (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (F : Type) [Field F] [CharP F p] (n : ℕ) (lam : ℕ → F)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F n ℓ) S₀ lam) :
    ∃ a : ℕ, a ≤ p - 1 ∧ ∃ j : ℕ, HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL F a).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F a ℓ) S₀ (fun ℓ => (ℓ : F) ^ j * lam ℓ) := by sorry
