-- Prove2me | Theorems.Thm_KhintchineTwoRegime_head_two_average_bound
-- name    : KhintchineTwoRegime.head_two_average_bound
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:31:31.915044+00:00
-- url     : https://prove2.me/theorems/b6dbc7bc-787e-412d-b439-ab9391785191
-- title:
--   Two-head averaging and sharp Khintchine for the tail
-- statement:
--   Let $n\ge2$ and let $\omega$ be a proper unit vector. Put $q=\omega_1+\omega_2$, $p=\omega_1-\omega_2$, and $c^2=\sum_{i\ge3}\omega_i^2$. Then
--
--   $$
--   K_n(\omega)\ \ge\ \frac q2+\frac{\sqrt{p^2+c^2}}{2\sqrt2}.
--   $$
--
--   This is the probabilistic input to the proof of Theorem 1. Averaging the first two signs expresses $K_n(\omega)$ using $\mathbb E\max\{q,|S|\}$ and $\mathbb E\max\{p,|S|\}$, where $S=\sum_{i\ge3}\omega_i\varepsilon_i$; the second average is $\mathbb E|p\varepsilon_0+S|$, to which the sharp $L^1$ Khintchine inequality applies.
--
--   **Formalization Note** Coordinates are zero-based, with `pad` giving $\omega_1$ and $\omega_2$. The finite sum with the condition $2\le i$ is exactly $c^2$.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, proof of Theorem 1, p.5 (averaging the first two signs and applying the sharp Khintchine inequality).

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_IsProper
import Definitions.Def_KhintchineTwoRegime_pad

theorem KhintchineTwoRegime.head_two_average_bound {n : ℕ} (hn : 2 ≤ n) (ω : Fin n → ℝ)
    (hω : IsProper ω) :
    (pad ω 0 + pad ω 1) / 2 +
      Real.sqrt ((pad ω 0 - pad ω 1) ^ 2 +
        ∑ i : Fin n, if 2 ≤ i.val then ω i ^ 2 else 0) / (2 * Real.sqrt 2) ≤
      K n ω := by sorry
