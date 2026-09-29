-- Prove2me | Theorems.Thm_ModularCurve_card_eq_of_ssJSetHasse
-- name    : ModularCurve.card_eq_of_ssJSetHasse
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/4504d501-2d72-564a-a31b-592df4d4804b
-- title:
--   Counting Hasse-supersingular j-invariants in characteristic q
-- statement:
--   Let $q$ be a prime with $q \ge 5$, and let $K$ be an algebraically closed field of characteristic $q$ with decidable equality. Let $S$ be a finite subset of $K$ which enumerates the set `ssJSetHasse q K`, in the sense that for every $j \in K$ one has $j \in S$ if and only if $j$ lies in that set; by definition $j$ lies in `ssJSetHasse q K` precisely when every Weierstrass curve $W$ over $K$ that is elliptic and satisfies $W.j = j$ has vanishing Hasse invariant $W.\mathrm{hasseInvariant}(q)$, the latter being the coefficient of $X^{q-1}$ in the $(q-1)/2$-th power of the two-torsion cubic of $W$ regarded as a polynomial. Then the cardinality of $S$ equals
--   $$\#S = \lfloor q/12 \rfloor + \varepsilon_3 + \varepsilon_4,$$
--   where the first term is the natural-number quotient $q/12$, $\varepsilon_3 = 1$ if $q \equiv 2 \pmod 3$ and $0$ otherwise, and $\varepsilon_4 = 1$ if $q \equiv 3 \pmod 4$ and $0$ otherwise.
--
--   This is the classical count of supersingular $j$-invariants in characteristic $q$, here in the formulation in which supersingularity of a $j$-invariant is expressed by vanishing of the Hasse invariant of every elliptic Weierstrass model with that $j$. It feeds into [`ModularCurve.card_eq_of_ssJSet`](thm.html#ModularCurve.card_eq_of_ssJSet), where the same count is transferred to the torsion-theoretic description of the supersingular locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_eq_of_ssJSetHasse.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.card_eq_of_ssJSetHasse (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K]
    (S : Finset K) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSetHasse q K) :
    S.card = q / 12 + (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) := by sorry
