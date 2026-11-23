-- Prove2me | Theorems.Thm_KhintchineTwoRegime_Phi_strict
-- name    : KhintchineTwoRegime.Phi_strict
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:39:40.217609+00:00
-- url     : https://prove2.me/theorems/d59c81a9-c7d2-4100-8b5d-7093116c594e
-- title:
--   Strict increase of $\Phi_q$ on the localized interval
-- statement:
--   For $\sqrt{483}/22\le q<1$ and $0<x\le1/12$,
--   $$
--   A(q)<\Phi_q(x),
--   $$
--   where
--   $$
--   A(q)=\frac{3q}{4}+\frac{3}{8\sqrt2}\sqrt{1-q^2},\qquad
--   \Phi_q(x)=\frac34q-\frac38x+\frac{\sqrt{1-q^2+qx}+2\sqrt{1-q^2+qx-x^2}}{8\sqrt2}.
--   $$
--   On this range both radicands are positive and at most $7/75$, and the derivative lower bound in the proof of Theorem 2 is strictly positive. Since $\Phi_q(0)=A(q)$, integration gives the strict comparison.
--
--   This calculus step excludes every localized competitor with $x>0$.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, proof of Theorem 2, p.8 (the estimate Phi'_q(x)>0 for 0<x<=1/12).

import Mathlib
import Definitions.Def_KhintchineTwoRegime_Phi
import Definitions.Def_KhintchineTwoRegime_Abound

theorem KhintchineTwoRegime.Phi_strict (q x : ℝ)
    (hq₁ : Real.sqrt 483 / 22 ≤ q) (hq₂ : q < 1)
    (hx₁ : 0 < x) (hx₂ : x ≤ 1 / 12) : Abound q < Phi q x := by sorry
