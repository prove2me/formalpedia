-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_diagonal_scaling_volume_toReal
-- name    : OAI.PiExponent.DeterminantContradiction.diagonal_scaling_volume_toReal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T14:56:28.147983+00:00
-- url     : https://prove2.me/theorems/96ed9b64-4fc5-45cd-86ca-5d8fe257540d
-- title:
--   Volume scaling under positive diagonal maps
-- statement:
--   For every measurable set in finite-dimensional real coordinate space, positive coordinatewise scaling changes volume by the product of the scale factors. This includes dimension zero, where the map and empty product are both trivial.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.diagonal_scaling_volume_toReal {m : Nat} (w : Fin m → Real) (hw : ∀ i, 0 < w i) (s : Set (Fin m → Real)) (hs : MeasurableSet s) :
    (MeasureTheory.volume ((fun x : Fin m → Real => fun i => w i * x i) '' s)).toReal =
      (∏ i : Fin m, w i) * (MeasureTheory.volume s).toReal := by sorry
