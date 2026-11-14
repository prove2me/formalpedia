-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_concave_test_perspective
-- name    : KSATSingleFlip.Connect.concave_test_perspective
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:28:28.18754+00:00
-- url     : https://prove2.me/theorems/d7f996f1-77b7-4051-a49c-370c15db73d1
-- title:
--   Concavity of the binary perspective of a concave test
-- statement:
--   For a concave test ψ on [0,1], the binary perspective (v₀+v₁)ψ(v₁/(v₀+v₁)) is jointly concave on pairs of nonnegative coordinates with positive total. This is the perspective inequality used in the single-clause comparison in Lemma 4.5.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false
open Set

theorem KSATSingleFlip.Connect.concave_test_perspective (ψ : ℝ → ℝ) (hψ : ConcaveOn ℝ (Icc 0 1) ψ)
    (x0 x1 y0 y1 a b : ℝ)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hy0 : 0 ≤ y0) (hy1 : 0 ≤ y1)
    (hxs : 0 < x0+x1) (hys : 0 < y0+y1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a*(x0+x1)*ψ (x1/(x0+x1)) + b*(y0+y1)*ψ (y1/(y0+y1)) ≤
      (a*(x0+x1)+b*(y0+y1))*ψ ((a*x1+b*y1)/(a*(x0+x1)+b*(y0+y1))) := by sorry
