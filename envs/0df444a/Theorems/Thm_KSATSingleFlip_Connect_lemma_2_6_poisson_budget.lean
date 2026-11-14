-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_poisson_budget
-- name    : KSATSingleFlip.Connect.lemma_2_6_poisson_budget
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:47:35.098438+00:00
-- url     : https://prove2.me/theorems/88f86718-52e5-432b-bca8-40beac5c8f82
-- title:
--   Numerical estimates for the Poisson-count argument
-- statement:
--   For positive n and a, a ≤ 1, L ≥ 1, and nonnegative ν, the displayed assumptions on count fluctuations and mean deviation imply the mean-comparison, count-range, and exponential-rate estimates used in the Poisson-count proof of Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false

theorem KSATSingleFlip.Connect.lemma_2_6_poisson_budget (ν a L n j : ℝ) (hν : 0 ≤ ν) (ha : 0 < a) (ha1 : a ≤ 1)
    (hL : 1 ≤ L) (hn : 0 < n) (hj : 0 ≤ j)
    (hclose : |j-ν*n| ≤ a*n/(4*L))
    (hsqrt : Real.sqrt (ν*n) ≤ a*n/(4*L)) :
    L*(|j-ν*n|+Real.sqrt (ν*n)) ≤ a*n/2 ∧
    j ≤ (ν+1)*n ∧
    (a*n/(4*L))^2 / (8*(ν*n + a*n/(4*L))) ≥ a^2*n/(128*(ν+1)*L^2) := by sorry
