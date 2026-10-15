-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_exists_degree_index_finset
-- name    : OAI.PiExponent.LogarithmicJetIdeals.exists_degree_index_finset
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:36:18.74304+00:00
-- url     : https://prove2.me/theorems/ed2b50ef-253f-4c51-97f7-e5a9cc94c809
-- title:
--   Finite set of multi-indices of a fixed degree
-- statement:
--   For a fixed finite number of coordinates and degree, the multi-indices of that degree form a finite set. The reduction uses this set to define the homogeneous correction as a finite polynomial sum.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.exists_degree_index_finset
    {n : Nat} (m : Nat) :
    ∃ S : Finset (Fin n → Nat),
      ∀ d : Fin n → Nat, d ∈ S ↔ (∑ k, d k) = m := by sorry
