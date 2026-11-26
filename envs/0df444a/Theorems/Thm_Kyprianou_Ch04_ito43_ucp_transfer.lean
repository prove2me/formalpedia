-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_ucp_transfer
-- name    : Kyprianou.Ch04.ito43_ucp_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:07:51.449801+00:00
-- url     : https://prove2.me/theorems/fc75508b-cbb9-4057-aee7-ccf81b473833
-- title:
--   Eventually exact error decomposition transfers uniform-in-probability convergence
-- statement:
--   Eventually exact error decomposition transfers uniform-in-probability convergence.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3, supporting lemma.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_add
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- An eventually exact decomposition of the error transfers uniform-in-probability convergence. -/

theorem Kyprianou.Ch04.ito43_ucp_transfer {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E G H : ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (hE : ∀ e : ℝ, 0 < e → Tendsto
      (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0))
    (hG : ∀ e : ℝ, 0 < e → Tendsto
      (fun n => (P {w | ∃ t ≤ T, e ≤ |G n t w|}).toReal) atTop (nhds 0))
    (hH : ∀ n : ℕ, 0 < n → ∀ t ≤ T, ∀ w, H n t w = E n t w + G n t w)
    (e : ℝ) (he : 0 < e) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |H n t w|}).toReal) atTop (nhds 0) := by sorry
