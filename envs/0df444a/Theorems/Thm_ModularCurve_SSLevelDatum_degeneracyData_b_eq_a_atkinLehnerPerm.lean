-- Prove2me | Theorems.Thm_ModularCurve_SSLevelDatum_degeneracyData_b_eq_a_atkinLehnerPerm
-- name    : ModularCurve.SSLevelDatum.degeneracyData_b_eq_a_atkinLehnerPerm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/29ebac16-19c0-51d6-baba-af44904d1a08
-- title:
--   Second degeneracy map equals first after Atkin–Lehner
-- statement:
--   Let $p$ be a prime, $K$ a field of characteristic $p$, and $M, s$ nonzero natural numbers. Let $X$ be a supersingular level datum of type `SSLevelDatum p K M s`, that is: the Laurent series $j(q^M)$ and $j(q^s)$ both lie in the intermediate field $F_{Ms} = K(j(q), j(q^{Ms}))$ of `LaurentSeries K`; the two $K$-algebra maps $F_M \to F_{Ms}$, namely the inclusion $\alpha$ (`levelAlphaC`) and the map $\beta$ (`levelBetaC`) induced by $q \mapsto q^s$, are integral, as are the analogous pairs `heckeAlphaC`, `heckeBetaC` at all auxiliary levels; restriction of a supersingular place of $F_{Ms}$ along $\alpha$ or along $\beta$ is a supersingular place of $F_M$; $X$ carries a $K$-algebra automorphism $\sigma$ of $F_{Ms}$ interchanging the generator $j(q)$ with $j(q^s)$ and the generator $j(q^{Ms})$ with $j(q^M)$, whose induced action on places preserves the set `ssPlaces p (M * s) K`; and $X$ carries modular polynomial data satisfying the Kronecker congruence at $p$. Let $W$ be a supersingular place of $F_{Ms}$. Then the second degeneracy map of `X.degeneracyData`, restriction of $W$ along $\beta$, coincides with the first, restriction along $\alpha$, evaluated at the place $\sigma$ transports $W$ to.
--
--   This is the standard compatibility $b = a \circ w_s$ between the two degeneracy maps $\Sigma(Ms) \to \Sigma(M)$ on supersingular points and the Atkin–Lehner involution in characteristic $p$. It feeds the combinatorial bookkeeping of the Čerednik–Drinfeld style degeneracy/Hecke data, and is used in the statements comparing degeneracy maps, place widths and adjoints of edge Hecke operators, and in the construction of matching Hecke data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSLevelDatum_degeneracyData_b_eq_a_atkinLehnerPerm.lean

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.SSLevelDatum.degeneracyData_b_eq_a_atkinLehnerPerm
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]
    (X : SSLevelDatum p K M s) (W : ↥(ssPlaces p (M * s) K)) :
    X.degeneracyData.b W = X.degeneracyData.a (X.atkinLehnerPerm W) := by sorry
