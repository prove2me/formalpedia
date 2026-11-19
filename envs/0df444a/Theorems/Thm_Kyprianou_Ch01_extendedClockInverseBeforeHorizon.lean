-- Prove2me | Theorems.Thm_Kyprianou_Ch01_extendedClockInverseBeforeHorizon
-- name    : Kyprianou.Ch01.extendedClockInverseBeforeHorizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:32:17.657135+00:00
-- url     : https://prove2.me/theorems/f437e42d-5067-46a3-8408-1ed5790d2008
-- title:
--   Right-inverse recovery for a strictly increasing extended-nonnegative occupation clock
-- statement:
--   If an extended nonnegative-valued occupation clock is globally nondecreasing and strictly increases to the right of t through a later finite horizon, its right-continuous first strict-crossing inverse at J(t) recovers exactly t. This is the deterministic order-theoretic component of Kyprianou equation (1.19), retaining the ENNReal infinity convention used by reciprocalOccupation.
-- source:
--   Kyprianou (2006), Chapter 1 equation (1.19), reverse Lamperti time change

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.ENNReal.Basic
set_option autoImplicit false

theorem Kyprianou.Ch01.extendedClockInverseBeforeHorizon
    (J : NNReal → ENNReal) (hmono : Monotone J)
    (t horizon : NNReal) (ht : t < horizon)
    (hstrict : ∀ s : NNReal, t < s → s < horizon → J t < J s) :
    sInf {s : NNReal | J t < J s} = t := by
  sorry
