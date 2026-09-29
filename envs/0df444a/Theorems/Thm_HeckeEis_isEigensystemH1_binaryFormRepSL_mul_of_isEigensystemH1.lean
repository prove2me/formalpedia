-- Prove2me | Theorems.Thm_HeckeEis_isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1
-- name    : HeckeEis.isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/6ae75835-da31-5575-ac4c-db2fa561296c
-- title:
--   Level raising at q for H¹ eigensystems when q+1 ≠ 0
-- statement:
--   Fix an integer $N \ge 1$, a prime $q$ with $q \nmid N$, a field $\kappa$ in which $(q+1)\cdot 1 \neq 0$, a set $S_0 \subseteq \mathbb{N}$, a natural number $n$ and a function $\mathrm{lam} : \mathbb{N} \to \kappa$. The coefficient module is [`HeckeEis.BinaryForm`](def/HeckeEis_BinaryFormRep.html#L25) $\kappa$ $n$, the submodule of degree-$n$ homogeneous elements of $\kappa[X_0,X_1]$, on which $\mathrm{SL}_2(\mathbb{Z})$ acts by [`HeckeEis.binaryFormRepSL`](def/HeckeEis_BinaryFormRep.html#L61), substituting $X_j \mapsto \sum_i M_{ij} X_i$; this representation is restricted along the inclusion of $\Gamma_0(M)$ into $\mathrm{SL}_2(\mathbb{Z})$, and the coefficient map at a prime $\ell$ is [`HeckeEis.binaryFormAlphaAdj`](def/HeckeEis_BinaryFormRep.html#L82) $\kappa$ $n$ $\ell$, substitution by $\mathrm{diag}(\ell,1)$, i.e. $P(X_0,X_1) \mapsto P(\ell X_0, X_1)$. Assume [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) holds at level $N$ for these data and the set $S_0$: there is a nonzero class $x$ in [`HeckeEis.coeffH1`](def/Gamma0CoeffCohomologyEigen.html#L16) of the restricted representation (the quotient of the module of cocycles by the coboundaries inside it) such that for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$ there is a $\kappa$-linear endomorphism $T$ of that $H^1$ which is a Hecke operator at $\ell$ in the sense of [`HeckeEis.IsCoeffHeckeOnH1`](def/Gamma0CoeffCohomologyEigen.html#L61) (every cocycle $z$ is carried by [`HeckeEis.coeffHeckeFun`](def/Gamma0CoeffCohomology.html#L129) to a cocycle $w$, and $T$ sends the class of $z$ to that of $w$), with $T x = \mathrm{lam}(\ell) \cdot x$. The conclusion asserts the same statement with $N$ replaced by $Nq$, with the same $\mathrm{lam}$, and with $S_0$ replaced by $S_0 \cup \{q\}$.
--
--   This is the level-raising step which allows one to pass from level $N$ to level $Nq$ for a given prime $q \nmid N$, at the cost of dropping the eigenvalue condition at $q$; the hypothesis that $q+1$ is invertible in $\kappa$ reflects the index $q+1$ occurring in the restriction–corestriction argument, and is automatic when $\kappa$ has characteristic $q$. It is used in the derivation of an eigensystem at a level divisible by a prescribed square factor, [`HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL`](thm.html#HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1
    (N : ℕ) [NeZero N] (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (κ : Type) [Field κ] (hq1 : ((q + 1 : ℕ) : κ) ≠ 0) (S₀ : Set ℕ) (n : ℕ) (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    HeckeEis.IsEigensystemH1 (N * q)
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 (N * q)).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) (insert q S₀) lam := by sorry
