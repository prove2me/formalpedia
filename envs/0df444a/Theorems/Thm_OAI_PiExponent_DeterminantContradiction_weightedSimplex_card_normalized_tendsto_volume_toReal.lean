-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_volume_toReal
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_volume_toReal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:44:06.809385+00:00
-- url     : https://prove2.me/theorems/9dc845f9-8f17-4ad9-98bd-267f331ce30d
-- title:
--   Weighted simplex lattice count converges to real volume
-- statement:
--   For positive weights and positive cutoff, the number of lattice points in the finite weighted-simplex definition, divided by H to the dimension, converges to the real-valued Lebesgue volume of the corresponding closed simplex. The finite coordinate bounds match the cutoff. A scaled-box argument controls the boundary contribution.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_volume_toReal {m : Nat} (w : Fin m → Real) (A : Real) (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    Tendsto (fun H : Real => ((realWeightedSimplex w (A * H)).card : Real) / H ^ m) atTop
      (nhds ((MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal)) := by sorry
