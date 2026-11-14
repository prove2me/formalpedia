-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_f_concave
-- name    : KSATSingleFlip.Connect.soft_field_f_concave
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:14:08.174299+00:00
-- url     : https://prove2.me/theorems/c8270e3f-e674-401b-8632-b2f4aa3dd18c
-- title:
--   Concavity of the soft-field mass test
-- statement:
--   The function f(q)=2√(q(1−q)) is concave on [0,1] and vanishes at both endpoints, so it is an admissible concave test for the soft-field order.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect Set

theorem KSATSingleFlip.Connect.soft_field_f_concave : ConcaveOn ℝ (Icc 0 1) fW ∧ fW 0 = 0 ∧ fW 1 = 0 := by sorry
