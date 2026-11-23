-- Prove2me | Theorems.Thm_KhintchineTwoRegime_q_ge_one_of_le_four
-- name    : KhintchineTwoRegime.q_ge_one_of_le_four
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:46:57.782898+00:00
-- url     : https://prove2.me/theorems/9a2d3b09-42ca-4a57-95f7-a9880c083376
-- title:
--   Low-dimensional proper vectors have $q=\omega_1+\omega_2\ge1$
-- statement:
--   For $2\le n\le4$, every proper unit vector $\omega\in\mathbb R^n$ satisfies
--   $$
--   q:=\omega_1+\omega_2\ge1.
--   $$
--
--   Indeed, properness and the normalization give
--   $$
--   1=\sum_{i=1}^n\omega_i^2\le \omega_1^2+(n-1)\omega_2^2
--    \le \omega_1^2+3\omega_2^2\le q^2.
--   $$
--   This is the low-dimensional part of Proposition 1; in particular, no such vector has $q<1$.
--
--   **Formalization Note** The coordinates $\omega_1,\omega_2$ are `pad ω 0` and `pad ω 1`; `IsProper` includes monotonicity, coordinatewise nonnegativity, and Euclidean unit norm.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, Proposition 1, p.5; Appendix A.4, p.15 (the bound q ≥ 1 for 2 ≤ n ≤ 4).

import Mathlib
import Definitions.Def_KhintchineTwoRegime_IsProper
import Definitions.Def_KhintchineTwoRegime_pad

theorem KhintchineTwoRegime.q_ge_one_of_le_four (n : ℕ) (hn₂ : 2 ≤ n) (hn₄ : n ≤ 4)
    (ω : Fin n → ℝ) (hω : KhintchineTwoRegime.IsProper ω) :
    1 ≤ KhintchineTwoRegime.pad ω 0 + KhintchineTwoRegime.pad ω 1 := by sorry
