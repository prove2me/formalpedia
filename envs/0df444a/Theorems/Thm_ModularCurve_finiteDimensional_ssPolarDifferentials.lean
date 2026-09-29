-- Prove2me | Theorems.Thm_ModularCurve_finiteDimensional_ssPolarDifferentials
-- name    : ModularCurve.finiteDimensional_ssPolarDifferentials
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/dbaccd87-64be-55fc-b549-f7fd02f88117
-- title:
--   Finite-dimensionality of supersingular polar differentials on X_{H'}(N)
-- statement:
--   Let $K$ be an algebraically closed field, $p$ a prime with $\operatorname{char} K = p$, let $N \ge 1$ and let $H'$ be a subgroup of $(\mathbb{Z}/N)^{\times}$. Write $\Gamma =$ [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image, under the inclusion of $\Gamma_0(N)$ into $\mathrm{SL}_2(\mathbb{Z})$, of the preimage of $H'$ under the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^{\times}$ sending $\gamma$ to the reduction of its lower-right entry. Let $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) be the intermediate field of $K((q))$ obtained by adjoining to $K$ the integral-form ratios `intFormRatiosC K Γ`, and let $S$ be the set of places of $F/K$ satisfying the predicate `IsSSPlaceQExp K Γ p` (the supersingular places in characteristic $p$). The statement asserts that the $K$-submodule of $\Omega[F/K]$ consisting of those $\omega$ such that, for every place $v$ of $F/K$, $\omega$ is regular at $v$ whenever $v \notin S$ and $\omega$ has at most a simple pole at $v$ whenever $v \in S$, is finite-dimensional over $K$. No dimension formula is claimed, only finiteness.
--
--   This is the finiteness half of the Riemann–Roch count for differentials with poles bounded by the supersingular locus of the modular curve of level $\Gamma_{H'}(N)$ in characteristic $p$. It underlies the comparison of the ordinary and supersingular contributions used in the construction of the twisted $\mathrm{dlog}$ map on torsion and in the Atkin–Lehner characterisation of regular differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finiteDimensional_ssPolarDifferentials.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.finiteDimensional_ssPolarDifferentials
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) :
    FiniteDimensional K ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH N H') p) := by sorry
