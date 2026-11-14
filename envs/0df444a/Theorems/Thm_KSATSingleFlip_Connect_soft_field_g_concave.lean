-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_g_concave
-- name    : KSATSingleFlip.Connect.soft_field_g_concave
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:14:03.731215+00:00
-- url     : https://prove2.me/theorems/e570eed9-bfc1-437d-9425-1eeeab2f56a3
-- title:
--   Concavity of the soft-field potential test
-- statement:
--   The function g(q)=2(√q+√(1−q)−1) is concave on [0,1] and vanishes at both endpoints, so it is an admissible concave test for the soft-field order.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect Set

theorem KSATSingleFlip.Connect.soft_field_g_concave : ConcaveOn ℝ (Icc 0 1) gW ∧ gW 0 = 0 ∧ gW 1 = 0 := by sorry
