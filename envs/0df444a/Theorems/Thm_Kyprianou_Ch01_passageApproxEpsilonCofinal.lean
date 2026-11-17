-- Prove2me | Theorems.Thm_Kyprianou_Ch01_passageApproxEpsilonCofinal
-- name    : Kyprianou.Ch01.passageApproxEpsilonCofinal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T19:00:45.993617+00:00
-- url     : https://prove2.me/theorems/ff00ff83-34a5-4203-bfaa-adcd0f729713
-- title:
--   The approach-horizon sequence is cofinal among positive time tolerances
-- statement:
--   Given two nonnegative times t<v, the positive sequence of approximation steps (v-t)/(n+2) eventually lies below every positive tolerance. This is an elementary Archimedean lemma used to prove a strict first-passage time is measurable in a strictly later natural sigma-field. Its conclusion neither assumes nor asserts that any passage event is measurable.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and Exercise 1.6(i), analytic auxiliary lemma for strict passage stopping time; original source milestone UUID 5623d362-55e7-4f38-be0c-f4933c607e17.

import Mathlib
open Set Filter
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.passageApproxEpsilonCofinal
    (t v : ℝ≥0) (htv : t < v) :
    ∀ e : ℝ≥0, 0 < e →
      ∃ n : ℕ, (v - t) / ((n : ℝ≥0) + 2) < e := by
  sorry
