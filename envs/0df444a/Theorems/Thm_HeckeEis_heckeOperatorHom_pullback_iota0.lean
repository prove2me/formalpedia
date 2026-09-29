-- Prove2me | Theorems.Thm_HeckeEis_heckeOperatorHom_pullback_iota0
-- name    : HeckeEis.heckeOperatorHom_pullback_iota0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/121735ef-b2e4-5644-bd78-054fb308d6a6
-- title:
--   Degeneracy pullback ι₀^* commutes with T_ℓ
-- statement:
--   Let $N, q, \ell$ be natural numbers with $\ell \neq 0$ and $\ell$ prime, let $\ell \nmid q$, let $A$ be an additive abelian group, and let $\varphi : \mathrm{Additive}(\Gamma_0(N)) \to A$ be an additive homomorphism. Write $T_\ell^{(M)}$ for `heckeOperatorHom M ℓ A`, the endomorphism of $\mathrm{Hom}(\mathrm{Additive}(\Gamma_0(M)), A)$ obtained by first pulling back along the homomorphism `heckeConj M ℓ` from `heckeUpper M ℓ` — the intersection inside $\Gamma_0(M)$ of the subgroup `heckeUpperSL ℓ` of $\mathrm{SL}_2(\mathbb{Z})$ — to $\Gamma_0(M)$, the map induced by the matrix conjugation `heckeConjMat ℓ`, and then applying the corestriction (transfer) `coresHom`, which sends $\psi$ to $g \mapsto \sum_{x \in \Gamma_0(M)/\mathrm{heckeUpper}(M,\ell)} \psi(\mathrm{transferAux}\,g\,x)$. Write $\iota_0^*$ for `pullbackHom (Ihara.ι₀ N q)`, precomposition with the homomorphism [`Ihara.ι₀ N q : \Gamma_0(N q) \to \Gamma_0(N)`](def/IharaIota.html#L17), a map $\mathrm{Hom}(\mathrm{Additive}(\Gamma_0(N)), A) \to \mathrm{Hom}(\mathrm{Additive}(\Gamma_0(Nq)), A)$. The assertion is the equality of homomorphisms $\iota_0^*\bigl(T_\ell^{(N)}\varphi\bigr) = T_\ell^{(Nq)}\bigl(\iota_0^*\varphi\bigr)$. No coprimality between $\ell$ and $N$, and no condition on $N$ or $q$ beyond $\ell \nmid q$, is imposed.
--
--   This is the Hecke-equivariance, away from the auxiliary level $q$, of one of the two degeneracy maps relating level $N$ and level $Nq$, expressed at the level of additive characters of $\Gamma_0$ with the Hecke operator realised as a transfer composed with a conjugation pullback. It is used in the level-raising analysis, where the $q$-new support of a normalised eigenform is compared along the degeneracy pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_heckeOperatorHom_pullback_iota0.lean

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_IharaIota

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup HeckeEis

theorem HeckeEis.heckeOperatorHom_pullback_iota0 (N q ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q) (φ : Additive (Gamma0 N) →+ A) :
    pullbackHom (Ihara.ι₀ N q) (heckeOperatorHom N ℓ A φ) =
      heckeOperatorHom (N * q) ℓ A (pullbackHom (Ihara.ι₀ N q) φ) := by sorry
