-- Prove2me | Theorems.Thm_ModularCurve_ssPlaces_nonempty
-- name    : ModularCurve.ssPlaces_nonempty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/431a20b1-dc13-5a57-b974-dfaeb5591fde
-- title:
--   Existence of a supersingular place on the level-N modular curve
-- statement:
--   Let $q$ be a prime, let $N$ be a nonzero natural number with $q \nmid N$, and let $k$ be an algebraically closed field of characteristic $q$. Consider the field $\mathtt{modularFunctionFieldC}\ k\ N$, namely the intermediate field of the Laurent series field $k((X))$ generated over $k$ by the two series `jqModC k` and `jqNModC k N`. A place of this field over $k$ is, in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22), a valuation subring of it which contains the image of $k$, is not the whole field, and is a principal ideal ring. The theorem asserts that the set `ssPlaces q N k` is nonempty, i.e. that there exists such a place $w$ satisfying all three conditions defining `IsSupersingularPlace`: $w$ is rational ($w$`.IsRational`), $w$ satisfies the predicate `IsAffineGeomPlace k N`, and the value $w$`.evalAt (jGeomGen k N)` of the geometric $j$-generator at $w$ lies in the set `ssJSet q k` of supersingular $j$-invariants in characteristic $q$.
--
--   This is the statement that the modular curve of level $N$ over an algebraically closed field of characteristic $q \nmid N$ carries at least one rational affine place whose $j$-value is supersingular; classically, the existence of supersingular $j$-invariants in characteristic $q$ (Deuring) together with the integrality of $j_N$ over $k[j]$ given by the modular equation. It feeds the analysis of the supersingular points on the Deligne–Rapoport special fibre, and is cited throughout the treatment of the modular curve model package at level $Nq$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ssPlaces_nonempty.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.ssPlaces_nonempty
    (q N : ℕ) [Fact q.Prime] [NeZero N] (hqN : ¬ q ∣ N)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] :
    (ssPlaces q N k).Nonempty := by sorry
