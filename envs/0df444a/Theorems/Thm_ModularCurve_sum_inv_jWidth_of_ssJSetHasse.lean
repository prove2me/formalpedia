-- Prove2me | Theorems.Thm_ModularCurve_sum_inv_jWidth_of_ssJSetHasse
-- name    : ModularCurve.sum_inv_jWidth_of_ssJSetHasse
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/59ad9b2d-7bd3-5a9e-b7c0-64aee6b152c1
-- title:
--   Eichler–Deuring mass formula in Hasse-invariant form
-- statement:
--   Let $q$ be a prime with $5 \le q$ and let $K$ be an algebraically closed field of characteristic $q$. Let $S$ be a finite subset of $K$ whose members are exactly the elements of `ssJSetHasse q K`, that is, the hypothesis is that $j \in S$ if and only if every Weierstrass curve $W$ over $K$ that is elliptic and satisfies $W.j = j$ has vanishing Hasse invariant, where `hasseInvariant q W` is defined as the coefficient of $X^{q-1}$ in the $((q-1)/2)$-th power of the polynomial attached to the two-torsion polynomial of $W$. Write `jWidth j` for the weight $3$ if $j = 0$, $2$ if $j = 1728$, and $1$ otherwise. The conclusion is the identity in $\mathbb{Q}$
--   $$\sum_{j \in S} \frac{1}{\mathrm{jWidth}(j)} = \frac{q-1}{12}.$$
--   Thus the hypothesis on $S$ both asserts that the set of Hasse-supersingular $j$-invariants is exhausted by the given finite set and fixes its members; the conclusion is the weighted count of that set.
--
--   This is the Eichler–Deuring mass formula for supersingular $j$-invariants in characteristic $q$, here with the weights $1/\mathrm{jWidth}(j) \in \{1, 1/2, 1/3\}$ recording the extra automorphisms at $j = 0$ and $j = 1728$, and with supersingularity expressed through vanishing of the Hasse invariant. It is used downstream to count supersingular $j$-invariants and to transfer the mass formula to other descriptions of the supersingular locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sum_inv_jWidth_of_ssJSetHasse.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial ModularCurve Finset

theorem ModularCurve.sum_inv_jWidth_of_ssJSetHasse (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] [DecidableEq K] (S : Finset K)
    (hS : ∀ j, j ∈ S ↔ j ∈ ssJSetHasse q K) :
    ∑ j ∈ S, ((jWidth j : ℚ))⁻¹ = ((q : ℚ) - 1) / 12 := by sorry
