-- Prove2me | Theorems.Thm_Ihara_exists_principalCongruenceAway_le_of_finiteIndex
-- name    : Ihara.exists_principalCongruenceAway_le_of_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/a9884c74-b96d-57a8-b660-fbba1607f092
-- title:
--   Congruence subgroup property of SL₂(ℤ[1/q])
-- statement:
--   Let $q$ be a prime number and let [`Ihara.ZAway q`](def/Gamma0Away.html#L11) denote the localisation of $\mathbb{Z}$ away from $q$, i.e. $\mathbb{Z}[1/q]$. Let $K$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z}[1/q])$ of finite index; $K$ is not assumed normal. The assertion is that there exist a natural number $M$ and a proof $h_{Mq}$ that $M$ is coprime to $q$ such that $M \neq 0$ and [`Ihara.principalCongruenceAway M q hMq`](def/IharaMennickeCarrier.html#L42) is contained in $K$. Here [`Ihara.principalCongruenceAway M q hMq`](def/IharaMennickeCarrier.html#L42) is the kernel of the homomorphism [`Ihara.slAwayReduction M q hMq`](def/IharaMennickeCarrier.html#L35) from $\mathrm{SL}_2(\mathbb{Z}[1/q])$ to $\mathrm{SL}_2(\mathbb{Z}/M)$ obtained by applying the ring homomorphism [`Ihara.zAwayToZMod M q hMq`](def/Gamma0AwayUnitsChar.html#L19) entrywise, that is, the principal congruence subgroup of level $M$, reduction modulo $M$ being defined on $\mathbb{Z}[1/q]$ precisely because $q$ is invertible modulo $M$. Thus every finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z}[1/q])$ contains a principal congruence subgroup of some nonzero level prime to $q$.
--
--   This is the congruence subgroup property for $\mathrm{SL}_2$ over $\mathbb{Z}[1/q]$ with $q$ prime, in Mennicke's form; the level is necessarily taken prime to $q$, since reduction modulo powers of $q$ is not defined on $\mathbb{Z}[1/q]$. It is used in the treatment of Ihara's group and of Hecke operators on the relevant congruence quotients, namely by [`Ihara.exists_coprime_forall_mem_Gamma_apply_eq_zero`](thm.html#Ihara.exists_coprime_forall_mem_Gamma_apply_eq_zero) and [`Ihara.heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel`](thm.html#Ihara.heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_exists_principalCongruenceAway_le_of_finiteIndex.lean

import Definitions.Def_IharaMennickeCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ihara.exists_principalCongruenceAway_le_of_finiteIndex {q : ℕ} (hq : q.Prime)
    (K : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Ihara.ZAway q))) [K.FiniteIndex] :
    ∃ (M : ℕ) (hMq : Nat.Coprime M q), M ≠ 0 ∧ Ihara.principalCongruenceAway M q hMq ≤ K := by sorry
