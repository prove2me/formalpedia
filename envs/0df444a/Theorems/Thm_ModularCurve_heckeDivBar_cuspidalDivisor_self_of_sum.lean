-- Prove2me | Theorems.Thm_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_sum
-- name    : ModularCurve.heckeDivBar_cuspidalDivisor_self_of_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/3ed91744-55d2-5030-8854-4096e9f22b24
-- title:
--   Uₚ fixes the cuspidal divisor from summed fibre data
-- statement:
--   Fix a non-zero natural number $p$. Let $\alpha =$ `heckeAlphaBar` and $\beta =$ `heckeBetaBar` be the two $\overline{\mathbb Q}$-algebra maps from the base-changed full modular function field of level $p$ into that of level $p\cdot p$ (the inclusion, respectively the map induced by $q \mapsto q^{p}$), and assume their underlying ring homomorphisms are integral, as expressed by `HeckeAlphaBarIntegral` and `HeckeBetaBarIntegral`; assume further that every non-zero element of `modularFunctionFieldBar (p * p)` has a degree-zero principal divisor. Places here are valuation subrings of the function field, proper, containing the image of $\overline{\mathbb Q}$ and principal-ideal rings. The data assumed are: a place $W_\infty$ of level $p^2$ whose $\beta$-fibre condition says that the fibre of `cuspInftyBar p` along $\beta$ is exactly $\{W_\infty\}$, with $e_\beta(W_\infty)\, f_\alpha(W_\infty) = p$ and $W_\infty$ restricting along $\alpha$ to `cuspInftyBar p`; a place $V_0$ and a finite set $S$ of places with $V_0 \notin S$ such that the $\beta$-fibre of `cuspZeroBar p` consists precisely of $V_0$ together with the members of $S$, with $e_\beta(V_0)\, f_\alpha(V_0) = 1$ and $V_0$ restricting along $\alpha$ to `cuspZeroBar p`, while $\sum_{V \in S} e_\beta(V)\, f_\alpha(V) = p - 1$ (in $\mathbb N$) and every $V \in S$ restricts along $\alpha$ to `cuspInftyBar p`. The conclusion is that the correspondence `heckeDivBar hα hβ`, namely pull-back along $\beta$ followed by push-forward along $\alpha$ on divisors of the level-$p$ field, fixes `cuspidalDivisor p` $= (\bar 0) - (\bar\infty)$.
--
--   This is the divisor-level statement that the $U_p$-correspondence on $X_0(p)$, realised through the two degeneracy maps to level $p^2$, fixes the cuspidal divisor $(\bar 0) - (\bar\infty)$; it is the form of the result depending only on summed ramification–inertia data over the two cusps. It is used by [`ModularCurve.heckeDivBar_cuspidalDivisor_self_of_prime`](thm.html#ModularCurve.heckeDivBar_cuspidalDivisor_self_of_prime), and through that by the statements about the cuspidal class in the degree-zero Picard group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeDivBar_cuspidalDivisor_self_of_sum.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.heckeDivBar_cuspidalDivisor_self_of_sum (p : ℕ) [NeZero p] (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p p) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) p p) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))] (Winf : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))) (hfibInf : ∀ W', W' ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) hβ (cuspInftyBar p) ↔ W' = Winf) (hWinf : Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) Winf * Place.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα Winf = p) (hrWinf : Winf.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα = cuspInftyBar p) (Vzero : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p))) (Smid : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (p * p)))) (hVzero : Vzero ∉ Smid) (hfibZero : ∀ V, V ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) hβ (cuspZeroBar p) ↔ V = Vzero ∨ V ∈ Smid) (hVzero1 : Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) Vzero * Place.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα Vzero = 1) (hrVzero : Vzero.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα = cuspZeroBar p) (hsumSmid : ∑ V ∈ Smid, Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) p p) V * Place.inertiaDegAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα V = p - 1) (hrSmid : ∀ V ∈ Smid, V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) p p) hα = cuspInftyBar p) : heckeDivBar hα hβ (cuspidalDivisor p) = cuspidalDivisor p := by sorry
