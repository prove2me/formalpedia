-- Prove2me | Theorems.Thm_ModularCurve_PDPairing_exists_forall_smul_eq_pairZ_and_perfect_mod_three
-- name    : ModularCurve.PDPairing.exists_forall_smul_eq_pairZ_and_perfect_mod_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/dc734c5d-191f-577e-94ee-917c86df4b81
-- title:
--   Parabolic pairings as a fixed multiple of mod-3 perfect forms
-- statement:
--   Assume that the principal congruence subgroup $\Gamma(4)\le SL_2(\mathbb{Z})$ is a free group (an instance hypothesis `IsFreeGroup ↥(Gamma 4)`). Then there is a single integer $c \neq 0$, independent of the level, such that for every natural number $M$ with $M \neq 0$ the following holds. Write $L_M$ for the $\mathbb{Z}$-module [`ModularCurve.Period.parabolicHoms ℤ (Gamma0 M) ℤ`](def/ModularCurve_PeriodMap.html#L62) of parabolic homomorphisms, that is, the submodule of additive homomorphisms $\varphi : \mathrm{Additive}\,\Gamma_0(M) \to \mathbb{Z}$ which vanish on every $\gamma \in \Gamma_0(M)$ whose matrix satisfies $(\operatorname{tr}\gamma)^2 = 4$. Then there exists a $\mathbb{Z}$-bilinear form $B : L_M \times L_M \to \mathbb{Z}$ (given as a $\mathbb{Z}$-linear map $L_M \to (L_M \to_{\mathbb{Z}} \mathbb{Z})$) such that: first, $c \cdot B$ equals the pairing [`ModularCurve.PDPairing.pairZ M`](def/ModularCurve_PDPairing.html#L654), whose value on $x,y$ is the natural-number quotient $48 / [\,\Gamma_0(M) : \Gamma_0(M) \cap \Gamma(4)\,]$, viewed in $\mathbb{Z}$, times `cuspSum` for $\Gamma_0(M) \cap \Gamma(4)$ of `hPrim` applied to the restrictions `resInf` of $x$ and $y$ to that subgroup; second, $B$ is perfect modulo $3$ in each variable separately, i.e. if $3 \mid B(x,y)$ for all $y \in L_M$ then $x = 3x'$ for some $x' \in L_M$, and symmetrically if $3 \mid B(x,y)$ for all $x \in L_M$ then $y = 3y'$ for some $y' \in L_M$.
--
--   This records integral Poincaré duality at the prime $3$ for the compact modular curves $X_0(M)$, in the guise of the parabolic cohomology $H^1_{\mathrm{par}}(\Gamma_0(M),\mathbb{Z})$: the uniformly normalised pairing `pairZ` is one fixed nonzero integer multiple, the same at all levels, of a bilinear form that is unimodular modulo $3$ on both sides. It is used by [`CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms`](thm.html#CohCarrier.exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms) and by [`LevelRaising.exists_parabolicPairings_perfect_mod_three`](thm.html#LevelRaising.exists_parabolicPairings_perfect_mod_three), where the mod-$3$ perfect forms supply the duality needed in the level-raising argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PDPairing_exists_forall_smul_eq_pairZ_and_perfect_mod_three.lean

import Definitions.Def_ModularCurve_PDPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem ModularCurve.PDPairing.exists_forall_smul_eq_pairZ_and_perfect_mod_three [IsFreeGroup ↥(Gamma 4)] :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ (M : ℕ) [NeZero M],
      ∃ B : ModularCurve.Period.parabolicHoms ℤ (Gamma0 M) ℤ →ₗ[ℤ]
          ModularCurve.Period.parabolicHoms ℤ (Gamma0 M) ℤ →ₗ[ℤ] ℤ,
        c • B = ModularCurve.PDPairing.pairZ M ∧
          (∀ x, (∀ y, (3 : ℤ) ∣ B x y) → ∃ x', x = (3 : ℤ) • x') ∧
          (∀ y, (∀ x, (3 : ℤ) ∣ B x y) → ∃ y', y = (3 : ℤ) • y') := by sorry
