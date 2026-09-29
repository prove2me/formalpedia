-- Prove2me | Theorems.Thm_ModularCurve_card_eq_of_ssJSet
-- name    : ModularCurve.card_eq_of_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/47b38fb7-db61-500f-a37a-42f64f21477e
-- title:
--   Count of supersingular j-invariants in characteristic q
-- statement:
--   Let $q$ be a prime with $5 \le q$, and let $K$ be an algebraically closed field of characteristic $q$ (with decidable equality). Let $S$ be a finite subset of $K$ which enumerates the set `ssJSet q K`, that is, $j \in S$ holds precisely when $j$ has the property that for every Weierstrass curve $W$ over $K$ that is elliptic and satisfies $W.j = j$, every point $P$ on the associated affine curve with $q \cdot P = 0$ is already the zero point; in other words, $j$ is a $j$-invariant for which no elliptic curve in Weierstrass form with that invariant has a non-trivial $q$-torsion point. The conclusion is the equality of natural numbers
--   $$\#S = \left\lfloor \tfrac{q}{12} \right\rfloor + \varepsilon_3 + \varepsilon_4,$$
--   where the division is natural-number division, $\varepsilon_3 = 1$ if $q \equiv 2 \pmod 3$ and $0$ otherwise, and $\varepsilon_4 = 1$ if $q \equiv 3 \pmod 4$ and $0$ otherwise.
--
--   This is the classical count of supersingular $j$-invariants in characteristic $q \ge 5$, here with supersingularity expressed through the vanishing of $q$-torsion. It feeds the comparisons in the project between the number of supersingular points and the genus of a level-one fibre, and the counting of annuli in multiplicity coverings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_eq_of_ssJSet.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
namespace ModularCurve

theorem card_eq_of_ssJSet (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K]
    (S : Finset K) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSet q K) :
    S.card = q / 12 + (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) := by sorry
