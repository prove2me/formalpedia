-- Prove2me | Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one
-- name    : ModularCurve.finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/2fc736a5-a891-5819-a00f-a178c6780e9b
-- title:
--   Rosenlicht count for the two-component curve at level Γ_{H'}(N)
-- statement:
--   Let $K$ be an algebraically closed field of characteristic a prime $p$, let $N \geq 1$ with $p \nmid N$, and let $H' \leq (\mathbb{Z}/N)^{\times}$ be a subgroup. Write $\Gamma =$ [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}(2,\mathbb{Z})$ obtained as the image, under the inclusion of $\Gamma_0(N)$, of the preimage of $H'$ under the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^{\times}$ sending a matrix to the reduction of its lower-right entry, and write $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $K((q))$ generated over $K$ by the quotients $\overline{p_f}/\overline{p_g}$ of reductions to $K$ of integral $q$-expansions $p_f, p_g \in \mathbb{Z}[[q]]$ of modular forms of level $\Gamma$ and equal weight, with $\overline{p_g} \neq 0$. Let $S =$ [`ModularCurve.ssNodePairsQExp K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L307) be the set of pairs $(v,w)$ of places of $F$ over $K$ (valuation subrings of $F$ containing $K$, proper, with principal ideals) such that $w$ satisfies the predicate `IsSSPlaceQExp` and $v$ is the image `qExpFrobeniusPlaceModL` of $w$, namely the restriction of $w$ along the mod-$p$ Frobenius endomorphism of $F$. The assertion is that the $K$-submodule [`ModularCurve.twoCompRegularDifferentials K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L320) of $\Omega_{F/K} \times \Omega_{F/K}$, defined as the $K$-span of the pairs of differentials satisfying `IsGluedPolarPair` relative to $S$, is finite-dimensional over $K$, and that its dimension plus $1$ equals $2\,g + \#S$, where $g$ is [`AlgebraicCurve.genusFF K F`](def/AlgebraicCurve_Repartitions.html#L145), the $K$-dimension of $H^1$ of the zero divisor of $F$, and $\#S$ is the cardinality of $S$.
--
--   This is the Rosenlicht-style dimension count for the regular differentials of the two-component curve obtained by glueing two copies of the mod-$p$ modular curve of level $\Gamma_{H'}(N)$ along the supersingular points, specialised from an arbitrary congruence subgroup to the level $\Gamma_{H'}(N)$ used in the level-lowering argument. It is used to compute the dimension of the space of mod-$p$ cusp forms of weight two entering the comparison with the two-component differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.finiteDimensional_and_finrank_twoCompRegularDifferentials_add_one
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (H' : Subgroup (ZMod N)ˣ) :
    FiniteDimensional K ↥(ModularCurve.twoCompRegularDifferentials K (CohCarrier.GammaH N H') p) ∧
      Module.finrank K ↥(ModularCurve.twoCompRegularDifferentials K (CohCarrier.GammaH N H') p) + 1 =
        2 * AlgebraicCurve.genusFF K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) +
          Nat.card ↥(ModularCurve.ssNodePairsQExp K (CohCarrier.GammaH N H') p) := by sorry
