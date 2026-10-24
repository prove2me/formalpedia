-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_fin_append_linear_isometry
-- name    : OAI.PiExponent.DeterminantContradiction.fin_append_linear_isometry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:49:15.22922+00:00
-- url     : https://prove2.me/theorems/13fea2fe-ff2f-4e08-bf2f-f32546404f07
-- title:
--   Bundle finite-coordinate append as a linear isometry
-- statement:
--   The append map is a linear isometric equivalence between a pair of finite real coordinate blocks and the concatenated block. Its explicit action lets the parent obtain the required `Fin.castSucc` and `Fin.last` equations after identifying the singleton block with `Real`.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Isometry
open scoped BigOperators
open MeasureTheory

theorem OAI.PiExponent.DeterminantContradiction.fin_append_linear_isometry (m : Nat) :
    ∃ e : ((Fin m → Real) × (Fin 1 → Real)) ≃ₗᵢ[Real] (Fin (m + 1) → Real),
      ∀ f g, e (f, g) = Fin.append f g := by sorry
