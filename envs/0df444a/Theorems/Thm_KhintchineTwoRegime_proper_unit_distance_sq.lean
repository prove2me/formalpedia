-- Prove2me | Theorems.Thm_KhintchineTwoRegime_proper_unit_distance_sq
-- name    : KhintchineTwoRegime.proper_unit_distance_sq
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:45:03.41858+00:00
-- url     : https://prove2.me/theorems/a97d09d3-e069-401f-a7ab-bc7b8614af8b
-- title:
--   Distance identity $\tau^2=2-\sqrt2\,q$ on the proper chamber
-- statement:
--   Let $n\ge2$ and let $\omega\in\mathcal C_n(\tau)$, so $\omega$ is a proper unit vector at Euclidean distance $\tau$ from $\omega^*=(1/\sqrt2,1/\sqrt2,0,\ldots,0)$. Writing $q=\omega_1+\omega_2$, the distance constraint expands to
--   $$
--   \tau^2=2-\sqrt2\,q.
--   $$
--
--   This elementary identity converts the distance hypothesis $\tau>\sqrt{2-\sqrt2}$ into the coefficient inequality $q<1$ used in Lemma 5.
--
--   **Formalization Note** Coordinates are zero-based and read through `pad`; the Euclidean norm is `l2Norm`. The dimension hypothesis is essential because `omegaStar` is truncated in lower dimensions.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, Appendix A.6, proof of Lemma 5, p.15 (the identity τ² = 2 − √2 q).

import Mathlib
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_pad

theorem KhintchineTwoRegime.proper_unit_distance_sq (n : ℕ) (hn : 2 ≤ n) (τ : ℝ)
    (ω : Fin n → ℝ) (hω : ω ∈ KhintchineTwoRegime.Cn n τ) :
    τ ^ 2 = 2 - Real.sqrt 2 *
      (KhintchineTwoRegime.pad ω 0 + KhintchineTwoRegime.pad ω 1) := by sorry
