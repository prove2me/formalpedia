-- Prove2me | Theorems.Thm_HeckeEis_heckeOperatorHom_pullback_iota1
-- name    : HeckeEis.heckeOperatorHom_pullback_iota1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/b86838bf-99e5-5fcd-bc8a-ff3380f41215
-- title:
--   Hecke equivariance of the degeneracy pullback ι₁^* at ℓ ∤ q
-- statement:
--   Let $N$, $q$ and $\ell$ be natural numbers with $\ell \neq 0$, let $A$ be an additive abelian group, and assume $\ell$ is prime and $\ell \nmid q$. Write $\iota_1 =$ [`Ihara.ι₁ N q`](def/IharaIota.html#L111) for the degeneracy homomorphism $\Gamma_0(Nq) \to \Gamma_0(N)$, and for a group homomorphism $f$ let `pullbackHom f` be the additive map $\varphi \mapsto \varphi \circ f$ on additive-group-valued homomorphisms. For a level $M$, the operator `heckeOperatorHom M ℓ A` on $\mathrm{Hom}(\Gamma_0(M)^{\mathrm{add}}, A)$ is the composite of pullback along `heckeConj M ℓ`, the homomorphism from the subgroup $\mathrm{heckeUpper}(M,\ell)$ of $\Gamma_0(M)$ — the elements of $\Gamma_0(M)$ lying in the subgroup `heckeUpperSL ℓ` of $\mathrm{SL}_2(\mathbb{Z})$ — to $\Gamma_0(M)$ induced by the matrix operation `heckeConjMat ℓ`, with the corestriction (transfer) map `coresHom`, which sends $\psi$ to $g \mapsto \sum_{x \in \Gamma_0(M)/\mathrm{heckeUpper}(M,\ell)} \psi(\mathrm{transferAux}\,(g,x))$. The assertion is that for every additive homomorphism $\varphi$ on $\Gamma_0(N)$ with values in $A$ one has the equality of additive homomorphisms on $\Gamma_0(Nq)$
--   $$\bigl(T_\ell^{(N)}\varphi\bigr) \circ \iota_1 \;=\; T_\ell^{(Nq)}\bigl(\varphi \circ \iota_1\bigr),$$
--   where $T_\ell^{(M)}$ denotes `heckeOperatorHom M ℓ A`.
--
--   This is the Hecke equivariance, away from the auxiliary prime-to-$\ell$ factor $q$, of the second degeneracy map between the congruence subgroups $\Gamma_0(Nq)$ and $\Gamma_0(N)$, expressed at the grain of additive characters (group cohomology in degree one) rather than of modular forms. It is used in the level-raising analysis, where the $q$-new support of a normalised eigenform is compared along the two degeneracy pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_heckeOperatorHom_pullback_iota1.lean

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_IharaIota

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup HeckeEis

theorem HeckeEis.heckeOperatorHom_pullback_iota1 (N q ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q) (φ : Additive (Gamma0 N) →+ A) :
    pullbackHom (Ihara.ι₁ N q) (heckeOperatorHom N ℓ A φ) =
      heckeOperatorHom (N * q) ℓ A (pullbackHom (Ihara.ι₁ N q) φ) := by sorry
