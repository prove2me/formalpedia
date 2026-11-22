-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_approximationFactor_ge_one
-- name    : MultiwayGap2325.Main.approximationFactor_ge_one
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:15:59.034389+00:00
-- url     : https://prove2.me/theorems/2269fb6b-8134-44ad-bc1b-e665fdb31d63
-- title:
--   Every random non-opposite cut has approximation factor at least one
-- statement:
--   For $q\ge2$, every random non-opposite cut of $\Delta_q$ satisfies $\alpha\ge1$.
--
--   Choose two distinct terminal vertices $e_i$ and $e_j$. Non-oppositeness forces their labels to be $i$ and $j$ in every realization, so the disagreement event has probability one. Since $d(e_i,e_j)=1$, the approximation inequality gives $1\le\alpha$.
--
--   **Formalization Note** This is the elementary positivity fact used when a flow certificate has nonpositive value $B-R$; it makes no assumptions beyond the definition of a random non-opposite cut and its approximation factor.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Definition 2.1 and equation (3), p.3; the observation “we always have α ≥ 1” in Proposition 3.2, p.5.

import Definitions.Def_MultiwayGap2325_Main_RandomCuts

open MeasureTheory Set
open MultiwayGap2325.Main
open scoped BigOperators ENNReal
universe u

/-- Two distinct vertices show that every approximation factor is at least one. -/
theorem MultiwayGap2325.Main.approximationFactor_ge_one
    (q : ℕ) (hq : 2 ≤ q) (Ξ : Type u) [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (α : ℝ) (hα : HasApproximationFactor C α) :
    1 ≤ α := by sorry
