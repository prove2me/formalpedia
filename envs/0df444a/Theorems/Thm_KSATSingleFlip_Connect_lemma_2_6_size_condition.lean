-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_size_condition
-- name    : KSATSingleFlip.Connect.lemma_2_6_size_condition
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:00:05.339366+00:00
-- url     : https://prove2.me/theorems/1e1e08c5-7fbd-4d2a-b9f9-fa4c8750f895
-- title:
--   An explicit size threshold for Poisson mean fluctuations
-- statement:
--   For positive a, L and n, if 16 L²ν ≤ a²n then √(νn) ≤ an/(4L). This makes the large-n condition in the Poisson-count proof of Lemma 2.6 explicit.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false

theorem KSATSingleFlip.Connect.lemma_2_6_size_condition (ν a L n : ℝ) (hν : 0 ≤ ν) (ha : 0 < a) (hL : 0 < L) (hn : 0 < n)
    (hsize : 16*L^2*ν ≤ a^2*n) :
    Real.sqrt (ν*n) ≤ a*n/(4*L) := by sorry
