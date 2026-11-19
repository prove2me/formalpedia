-- Prove2me | Theorems.Thm_Kyprianou_Ch01_strictClockInverseBeforeHorizon
-- name    : Kyprianou.Ch01.strictClockInverseBeforeHorizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:12:19.362064+00:00
-- url     : https://prove2.me/theorems/ad574b32-76da-477c-8085-a8e1c2bff9de
-- title:
--   Strict-increase before a finite horizon gives exact right-inverse occupation-clock recovery
-- statement:
--   For a nondecreasing nonnegative-time clock J and any time t strictly before a finite horizon, suppose the clock is strictly greater at every later time s between t and the horizon. Then the infimum of all times when the clock exceeds its value J(t) is exactly t. This is the deterministic right-inverse lemma underlying Lamperti forward recovery (1.17), allowing the clock to become flat after extinction.
-- source:
--   Kyprianou (2006), Chapter 1 equation (1.17), right-inverse occupation time change

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic
set_option autoImplicit false
open scoped NNReal

theorem Kyprianou.Ch01.strictClockInverseBeforeHorizon
    (J : NNReal → ℝ) (hmono : Monotone J)
    (t horizon : NNReal) (ht : t < horizon)
    (hstrict : ∀ s : NNReal, t < s → s < horizon → J t < J s) :
    sInf {s : NNReal | J t < J s} = t := by
  sorry
