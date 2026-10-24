-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_scalar_preimage
-- name    : OAI.PiExponent.DeterminantContradiction.volume_scalar_preimage
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:03:32.380327+00:00
-- url     : https://prove2.me/theorems/058651a3-e229-4f66-8116-91d2c93afb19
-- title:
--   Volume of a scalar linear-map preimage
-- statement:
--   For any set in finite-dimensional real coordinate space, preimage under scalar dilation by r⁻¹ has volume rⁿ times the set's volume. This is the scalar-map case of the linear-map Lebesgue volume formula: the dilation determinant is r⁻ⁿ, so the map's measure factor is its reciprocal, rⁿ. No measurability hypothesis on s is needed for the measure-map equality. The argument includes dimension zero, where the determinant and scaling factor are 1.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.volume_scalar_preimage
    (n : Nat) (r : Real) (hpos : 0 < r) (s : Set (Fin n → Real)) :
    MeasureTheory.volume ((fun y : Fin n → Real => r⁻¹ • y) ⁻¹' s) =
      ENNReal.ofReal (r ^ n) * MeasureTheory.volume s := by sorry
