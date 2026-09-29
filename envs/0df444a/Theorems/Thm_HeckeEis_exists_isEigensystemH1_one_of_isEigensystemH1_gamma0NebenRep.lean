-- Prove2me | Theorems.Thm_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep
-- name    : HeckeEis.exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/3f7057d0-7662-50fd-91e8-ee4ec546b0dc
-- title:
--   Twisting a mod-p nebentypus eigensystem to trivial nebentypus
-- statement:
--   Let $p$ be a prime, $M \ge 1$ an integer with $p \mid M$, $S_0$ a set of natural numbers, and $e,t$ natural numbers with $(p-1) \mid e + 2t$. Let $\kappa$ be a field of characteristic $p$ and $\nu \colon \mathbb{N} \to \kappa$ a function. Write $\rho_e =$ [`HeckeEis.gamma0NebenRep p M hpM κ e`](def/HeckeEis_Gamma0NebenRep.html#L22) for the one-dimensional representation of $\Gamma_0(M)$ on $\kappa$ in which $\gamma$ acts by multiplication by the $e$-th power of the image in $\kappa$ of the lower-right entry of $\gamma$ reduced modulo $p$. Assume [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) holds for $M$, $\rho_e$, the constant family of coefficient maps $\ell \mapsto \mathrm{id}_\kappa$ and the set $S_0$ with eigenvalues $\nu$: that is, there is a nonzero class $x$ in `coeffH1` of $\rho_e$ (the quotient of the cocycles `coeffCocycles` by the coboundaries `coeffCoboundaries`) such that for every prime $\ell$ with $\ell \nmid M$ and $\ell \notin S_0$ there is a $\kappa$-linear endomorphism $T$ of `coeffH1` induced, in the sense of `IsCoeffHeckeOnH1`, by the explicit cocycle-level Hecke operator `coeffHeckeFun M ℓ` with coefficient map $\mathrm{id}$, and $Tx = \nu(\ell)\,x$. Then there exist a natural number $M'$ and a function $\mu \colon \mathbb{N} \to \kappa$ such that $M \mid M'$, $M' \mid Mp$, the same eigensystem property `IsEigensystemH1` holds at level $M'$ for the trivial representation $1$ of $\Gamma_0(M')$ on $\kappa$, with identity coefficient maps, the set $\{p\} \cup S_0$ and eigenvalues $\mu$, and $\mu(\ell) = \ell^{\,t}\,\nu(\ell)$ for every prime $\ell$ with $\ell \nmid M$, $\ell \ne p$ and $\ell \notin S_0$.
--
--   This is the twisting step which removes the nebentypus at $p$: a weight-two mod-$p$ eigensystem on $\Gamma_0(M)$ with coefficients in the $e$-th power of the mod-$p$ character given by the lower-right entry is replaced, after twisting the eigenvalues by $\ell^{\,t}$, by an eigensystem with trivial coefficients at a level dividing $Mp$. It is used in [`HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL`](thm.html#HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_Gamma0NebenRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (S₀ : Set ℕ) (e t : ℕ)
    (het : (p - 1) ∣ e + 2 * t)
    (κ : Type) [Field κ] [CharP κ p] (nu : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 M (HeckeEis.gamma0NebenRep p M hpM κ e)
      (fun _ => LinearMap.id) S₀ nu) :
    ∃ (M' : ℕ) (mu : ℕ → κ), M ∣ M' ∧ M' ∣ M * p ∧
      HeckeEis.IsEigensystemH1 M' (1 : Representation κ (CongruenceSubgroup.Gamma0 M') κ)
        (fun _ => LinearMap.id) (insert p S₀) mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ p → ℓ ∉ S₀ → mu ℓ = (ℓ : κ) ^ t * nu ℓ := by sorry
