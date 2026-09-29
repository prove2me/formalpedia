-- Prove2me | Theorems.Thm_HeckeEis_isEigensystemH1_one_natCast_add_one
-- name    : HeckeEis.isEigensystemH1_one_natCast_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/6ad3414c-fc32-5902-bfec-a73404c61c11
-- title:
--   Eisenstein eigensystem ℓ↦ℓ+1 in H¹(Γ₀(M),κ)
-- statement:
--   Let $M$ be a natural number with $2 \le M$, let $\kappa$ be a field, and let $S_0$ be an arbitrary set of natural numbers. Consider the trivial one-dimensional representation $1$ of $\Gamma_0(M)$ on $\kappa$ over $\kappa$, and the constant family of coefficient maps $\ell \mapsto \mathrm{id}_\kappa$. The assertion is that the predicate [`HeckeEis.IsEigensystemH1`](def/Gamma0CoeffCohomologyEigen.html#L72) holds for these data with eigenvalue system $\ell \mapsto (\ell : \kappa) + 1$; unfolding the definition, there exists a class $x$ in [`HeckeEis.coeffH1`](def/Gamma0CoeffCohomologyEigen.html#L16) of the trivial representation — the quotient of the submodule [`HeckeEis.coeffCocycles`](def/Gamma0CoeffCohomology.html#L13) of functions $\Gamma_0(M) \to \kappa$ by the part of [`HeckeEis.coeffCoboundaries`](def/Gamma0CoeffCohomology.html#L45) lying in it — such that $x \ne 0$ and, for every prime $\ell$ with $\ell \nmid M$ and $\ell \notin S_0$, there is a $\kappa$-linear endomorphism $T$ of this quotient which is a Hecke operator at $\ell$ in the sense of [`HeckeEis.IsCoeffHeckeOnH1`](def/Gamma0CoeffCohomologyEigen.html#L61) with coefficient map $\mathrm{id}_\kappa$ (for every cocycle $z$ the function [`HeckeEis.coeffHeckeFun`](def/Gamma0CoeffCohomology.html#L129) $M$ $\ell$ applied to $z$ is again a cocycle $w$, and $T$ sends the class of $z$ to the class of $w$) and which satisfies $T x = ((\ell : \kappa) + 1) \cdot x$. No hypothesis restricts the characteristic of $\kappa$ or the set $S_0$.
--
--   For trivial coefficients the classes in question are homomorphisms $\Gamma_0(M) \to \kappa$, and over $\mathbb{C}$ the eigenclass produced here is the one attached to the Eisenstein series $E_2(z) - M E_2(Mz)$; the statement provides the Eisenstein eigensystem $\ell \mapsto \ell+1$ at every level $M \ge 2$ and over every field, with no constraint on the characteristic. It is used by [`HeckeEis.exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep`](thm.html#HeckeEis.exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep), where eigensystems are transported through filtrations of coefficient modules whose connecting maps create or destroy exactly the systems $\ell + 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isEigensystemH1_one_natCast_add_one.lean

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isEigensystemH1_one_natCast_add_one (M : ℕ) (hM : 2 ≤ M) (κ : Type) [Field κ]
    (S₀ : Set ℕ) :
    HeckeEis.IsEigensystemH1 M (1 : Representation κ (CongruenceSubgroup.Gamma0 M) κ)
      (fun _ => LinearMap.id) S₀ (fun ℓ => (ℓ : κ) + 1) := by sorry
