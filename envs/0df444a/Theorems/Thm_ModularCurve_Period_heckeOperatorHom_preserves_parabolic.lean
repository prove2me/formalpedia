-- Prove2me | Theorems.Thm_ModularCurve_Period_heckeOperatorHom_preserves_parabolic
-- name    : ModularCurve.Period.heckeOperatorHom_preserves_parabolic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/964b4f4a-30ab-5aaf-80f3-44fdca204324
-- title:
--   Hecke operators preserve parabolic homomorphisms on Γ₀(N)
-- statement:
--   Let $N$ and $\ell$ be natural numbers with $\ell \neq 0$, let $A$ be an additive abelian group, and let $\varphi : \mathrm{Additive}(\Gamma_0(N)) \to A$ be an additive homomorphism, that is, a homomorphism from $\Gamma_0(N)$ (written multiplicatively) to $A$. Call such a homomorphism parabolic, in the sense of [`ModularCurve.Period.IsParabolicHom`](def/ModularCurve_PeriodMap.html#L15), when it vanishes on every $\gamma \in \Gamma_0(N)$ whose image matrix in $\mathrm{M}_2(\mathbb{Z})$ satisfies $\mathrm{tr}(\gamma)^2 = 4$. The assertion is that if $\varphi$ is parabolic then so is [`HeckeEis.heckeOperatorHom N ℓ A φ`](def/Gamma0HeckeOperatorHom.html#L285), the image of $\varphi$ under the Hecke operator at $\ell$, which is defined as the composite of pullback along the homomorphism `heckeConj N ℓ` from the finite-index subgroup `heckeUpper N ℓ` $=$ `(heckeUpperSL ℓ).subgroupOf (Gamma0 N)` into $\Gamma_0(N)$, given by the conjugation operation `heckeConjMat ℓ` on matrices, followed by the additive corestriction (transfer) `coresHom (heckeUpper N ℓ)`, which sends $\psi$ to $g \mapsto \sum_{q \in \Gamma_0(N)/\,H} \psi(\mathrm{transferAux}\,H\,g\,q)$. No primality of $\ell$ or condition relating $\ell$ to $N$ is assumed, so the statement covers both $T_\ell$ for $\ell \nmid N$ and $U_q$ for $q \mid N$.
--
--   This is the stability of the parabolic (cuspidal) part of $\mathrm{Hom}(\Gamma_0(N), A)$ under the Hecke action: the parabolic condition is imposed by vanishing at elements of trace $\pm 2$, and the double-coset/transfer description of $T_\ell$ respects it. It is used in the construction of the Hecke action on parabolic homomorphism groups and on the corresponding degree-one cohomology, in particular in the rank computations for the Hecke-stable pieces attached to non-Eisenstein maximal ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.lean

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup

theorem ModularCurve.Period.heckeOperatorHom_preserves_parabolic (N ℓ : ℕ) [NeZero ℓ]
    (A : Type*) [AddCommGroup A] (φ : Additive (Gamma0 N) →+ A)
    (hφ : ModularCurve.Period.IsParabolicHom (Gamma0 N) φ) :
    ModularCurve.Period.IsParabolicHom (Gamma0 N) (HeckeEis.heckeOperatorHom N ℓ A φ) := by sorry
