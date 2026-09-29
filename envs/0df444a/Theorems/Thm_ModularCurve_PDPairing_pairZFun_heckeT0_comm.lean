-- Prove2me | Theorems.Thm_ModularCurve_PDPairing_pairZFun_heckeT0_comm
-- name    : ModularCurve.PDPairing.pairZFun_heckeT0_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/6a75e2a7-0f3b-54f0-b303-14b3f0db32d7
-- title:
--   Hecke self-adjointness of the integer pairing on parabolic classes
-- statement:
--   Let $N$ and $\ell$ be nonzero natural numbers, with $\ell$ prime and $\ell \nmid N$, and assume that the principal congruence subgroup $\Gamma(4) \le \mathrm{SL}_2(\mathbb{Z})$ is free as a group. Let $\varphi, \psi \colon \mathrm{Additive}\,\Gamma_0(N) \to \mathbb{Z}$ be additive homomorphisms (i.e. homomorphisms $\Gamma_0(N) \to \mathbb{Z}$ written additively) which are parabolic in the sense of `IsParabolicHom`: each vanishes on every $\gamma \in \Gamma_0(N)$ whose integral $2 \times 2$ matrix satisfies $(\operatorname{tr} \gamma)^2 = 4$. The assertion is that the integer pairing `pairZFun N` is symmetric with respect to the operator `heckeT0 N ℓ ℤ`, namely $\langle T_\ell \varphi, \psi\rangle = \langle \varphi, T_\ell \psi\rangle$. Here `heckeT0 N ℓ ℤ` is the additive endomorphism of $\mathrm{Hom}(\Gamma_0(N), \mathbb{Z})$ obtained by composing a character with the homomorphism `conjL0 N ℓ` from `Gamma0HUpper N ℓ` to $\Gamma_0(N)$, given by conjugation by the upper-triangular matrix attached to $\ell$, and then applying the group-theoretic transfer back to $\Gamma_0(N)$; and `pairZFun N φ ψ` is the integer $48 / [\Gamma_0(N) : \Gamma_0(N) \cap \Gamma(4)]$ times the sum, over the cusps of $\Gamma_0(N) \cap \Gamma(4)$, of the quantity `hPrim` formed from the restrictions of $\varphi$ and $\psi$ to $\Gamma_0(N) \cap \Gamma(4)$ evaluated at the chosen cusp generators.
--
--   This is the self-adjointness (Hecke equivariance) of the integral period pairing on parabolic homomorphisms of $\Gamma_0(N)$ with respect to $T_\ell$ for $\ell \nmid N$. It is used in the level-raising part of the argument, in [`LevelRaising.exists_parabolicPairings_perfect_mod_three`](thm.html#LevelRaising.exists_parabolicPairings_perfect_mod_three) and in [`LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime`](thm.html#LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PDPairing_pairZFun_heckeT0_comm.lean

import Definitions.Def_ModularCurve_PDPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup ModularCurve.Period in

theorem ModularCurve.PDPairing.pairZFun_heckeT0_comm (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
    [IsFreeGroup ↥(Gamma 4)] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) (hφ : IsParabolicHom (Gamma0 N) φ) (hψ : IsParabolicHom (Gamma0 N) ψ) :
    ModularCurve.PDPairing.pairZFun N (ModularCurve.PDPairing.heckeT0 N ℓ ℤ φ) ψ =
      ModularCurve.PDPairing.pairZFun N φ (ModularCurve.PDPairing.heckeT0 N ℓ ℤ ψ) := by sorry
