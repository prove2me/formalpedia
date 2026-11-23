-- Prove2me | Theorems.Thm_KhintchineTwoRegime_fourProfile_attains_bound
-- name    : KhintchineTwoRegime.fourProfile_attains_bound
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:34:11.530806+00:00
-- url     : https://prove2.me/theorems/57583602-92de-4c24-96ca-b5f33fc26d4d
-- title:
--   The four-coordinate profile belongs to $\mathcal C_n(\tau)$ and attains the bound
-- statement:
--   For $n\ge4$ and $0\le\tau\le\sqrt{2-\sqrt2}$, let $\omega_\tau=(r,r,s,s,0,\ldots,0)$, where
--
--   $$
--   r=\frac{1-\tau^2/2}{\sqrt2},\qquad s=\frac{\tau}{\sqrt2}\sqrt{1-\frac{\tau^2}{4}}.
--   $$
--
--   Then $\omega_\tau\in\mathcal C_n(\tau)$ and
--
--   $$
--   K_n(\omega_\tau)=\frac1{\sqrt2}+
--   \Bigl(\sqrt{1-\frac{\tau^2}{4}}-\tau\Bigr)\frac{\tau}{2\sqrt2}.
--   $$
--
--   Thus the lower bound of Theorem 1 is attained throughout the four-coordinate regime, including both endpoints.
--
--   **Formalization Note** Membership in $\mathcal C_n(\tau)$ includes properness, unit Euclidean norm, and distance exactly $\tau$ from $\omega^*$.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, Theorem 1, p.4, and the converse attainment computation in its proof, p.5.

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_fourProfile

theorem KhintchineTwoRegime.fourProfile_attains_bound (n : ℕ) (hn : 4 ≤ n) (τ : ℝ)
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ Real.sqrt (2 - Real.sqrt 2)) :
    fourProfile n τ ∈ Cn n τ ∧
      K n (fourProfile n τ) =
        1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) := by sorry
