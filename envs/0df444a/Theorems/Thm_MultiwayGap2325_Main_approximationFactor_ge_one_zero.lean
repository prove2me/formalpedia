-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_approximationFactor_ge_one_zero
-- name    : MultiwayGap2325.Main.approximationFactor_ge_one_zero
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-22T23:19:08.956749+00:00
-- url     : https://prove2.me/theorems/becd5213-7104-4aec-bab0-dc37c1cf4739
-- title:
--   Approximation factor at least one, on ordinary probability spaces
-- statement:
--   For $q\ge2$, every random non-opposite cut on an ordinary `Type 0` probability space has approximation factor $\alpha\ge1$.
--
--   At two distinct terminal vertices $e_i,e_j$, non-oppositeness makes the labels different with probability one, and $d(e_i,e_j)=1$. Equation (3) therefore specializes to $1\le\alpha$.
--
--   **Formalization Note** This is the `Type 0` case needed by Lemma 2.2. It is stated separately so that its direct proof does not depend on universe-polymorphic statement matching.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Definition 2.1 and equation (3), p.3; observation “we always have α ≥ 1” in Proposition 3.2, p.5.

import Definitions.Def_MultiwayGap2325_Main_RandomCuts

open MeasureTheory Set
open MultiwayGap2325.Main
open scoped BigOperators ENNReal

/-- Two distinct vertices show that every approximation factor is at least one. -/
theorem MultiwayGap2325.Main.approximationFactor_ge_one_zero
    (q : ℕ) (hq : 2 ≤ q) (Ξ : Type) [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (α : ℝ) (hα : HasApproximationFactor C α) :
    1 ≤ α := by sorry
