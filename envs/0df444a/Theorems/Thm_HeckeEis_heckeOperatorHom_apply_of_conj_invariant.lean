-- Prove2me | Theorems.Thm_HeckeEis_heckeOperatorHom_apply_of_conj_invariant
-- name    : HeckeEis.heckeOperatorHom_apply_of_conj_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/17673384-ef35-553d-85ef-470a968d5688
-- title:
--   Hecke operator acts by the index on conjugation-invariant characters
-- statement:
--   Let $N$ and $\ell$ be natural numbers with $\ell \neq 0$, let $A$ be an additive commutative group, and let $\varphi$ be an additive homomorphism from `Additive (Gamma0 N)`, the group $\Gamma_0(N)$ written additively, to $A$. Write $H =$ `heckeUpper N ℓ` for the subgroup of $\Gamma_0(N)$ consisting of those $\gamma$ whose upper right entry $\gamma_{01}$ is divisible by $\ell$, and let `heckeConj N ℓ` be the group homomorphism $H \to \Gamma_0(N)$ sending a matrix with entries $a,b,c,d$ to the matrix with entries $a,\ b/\ell,\ c\ell,\ d$ (a matrix of determinant $1$ lying again in $\Gamma_0(N)$). Assume $\varphi$ is invariant under this conjugation map: $\varphi(\mathrm{heckeConj}\,\gamma) = \varphi(\gamma)$ for every $\gamma \in H$. Then for every $g$ in `Additive (Gamma0 N)`, the value at $g$ of `heckeOperatorHom N ℓ A φ`, that is, of the corestriction (transfer) from $H$ to $\Gamma_0(N)$ applied to the pullback of $\varphi$ along `heckeConj N ℓ`, equals $[\Gamma_0(N) : H] \cdot \varphi(g)$, the integer multiple of $\varphi(g)$ by the index of $H$.
--
--   This is the push–pull (projection) formula for the transfer in degree one: on characters invariant under the Hecke conjugation, the Hecke operator built as transfer composed with pullback degenerates to multiplication by the index $[\Gamma_0(N):H]$. It is used by [`HeckeEis.heckeOperatorHom_apply_of_factorsThroughEntry`](thm.html#HeckeEis.heckeOperatorHom_apply_of_factorsThroughEntry), and together with the index computation it produces the eigenvalue $\ell+1$ for Eisenstein-type characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_heckeOperatorHom_apply_of_conj_invariant.lean

import Definitions.Def_Gamma0HeckeOperatorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup Subgroup

theorem HeckeEis.heckeOperatorHom_apply_of_conj_invariant (N ℓ : ℕ) [NeZero ℓ] {A : Type*}
    [AddCommGroup A] (φ : Additive ↥(Gamma0 N) →+ A)
    (hφ : ∀ γ : ↥(HeckeEis.heckeUpper N ℓ),
      φ (Additive.ofMul ((HeckeEis.heckeConj N ℓ) γ)) = φ (Additive.ofMul ↑γ))
    (g : Additive ↥(Gamma0 N)) :
    HeckeEis.heckeOperatorHom N ℓ A φ g = (HeckeEis.heckeUpper N ℓ).index • φ g := by sorry
