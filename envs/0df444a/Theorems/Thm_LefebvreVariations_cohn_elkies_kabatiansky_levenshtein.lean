-- Prove2me | Theorems.Thm_LefebvreVariations_cohn_elkies_kabatiansky_levenshtein
-- name    : LefebvreVariations.cohn_elkies_kabatiansky_levenshtein
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:30:53.314812+00:00
-- url     : https://prove2.me/theorems/06dd1b06-823c-4ce5-a5c1-7e1693ca2655
-- title:
--   Lefebvre's variations, No. 23 — on a theme by Cohn and Elkies: Cohn–Elkies auxiliary functions reach the Kabatiansky–Levenshtein exponent (Cohn–Zhao)
-- statement:
--   This is the statement that the Cohn–Elkies linear-programming bound for sphere packing reaches the Kabatiansky–Levenshtein exponent: in all large dimensions there are Cohn–Elkies auxiliary functions certifying $\Delta_d \le 2^{-(0.599-\varepsilon)d}$.
--
--   For every $\varepsilon > 0$ there is $N$ such that for every dimension $d \ge N$ there exists a Schwartz function $f : \mathbb{R}^d \to \mathbb{C}$ such that
--   1. $f$ is real-valued and its Fourier transform $\widehat f(\xi) = \int_{\mathbb{R}^d} f(x)\, e^{-2\pi i \langle x, \xi\rangle}\,dx$ is real-valued;
--   2. $f(x) \le 0$ whenever $|x| \ge 1$;
--   3. $\widehat f(\xi) \ge 0$ for all $\xi$, and $\widehat f(0) > 0$;
--   4. $$\frac{f(0)}{\widehat f(0)}\,\operatorname{vol}\bigl(B(0,\tfrac12)\bigr) \;\le\; 2^{-(0.599-\varepsilon)\,d}, \qquad \operatorname{vol}\bigl(B(0,\tfrac12)\bigr) = \frac{\pi^{d/2}}{2^d\,\Gamma(d/2+1)} .$$
--
--   By the Cohn–Elkies theorem, any such $f$ shows that every packing of unit-diameter balls (centres at mutual distance $\ge 1$) in $\mathbb{R}^d$ has density at most the left-hand side of 4. Cohn and Zhao proved that the Cohn–Elkies bound is always at least as strong as the Kabatiansky–Levenshtein bound $\Delta_d \le 2^{-(0.5990\ldots+o(1))d}$ (an analogue of Rodemich's theorem in coding theory), which gives the statement since $0.59905\ldots > 0.599$.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin d)`, `f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)` is a Schwartz function and `𝓕 f` is Mathlib's Fourier transform (with the $e^{-2\pi i\langle x,\xi\rangle}$ normalisation), so `𝓕 f 0` $= \int f$. Real-valuedness is written `((f x).re : ℂ) = f x`, the same form as the hypotheses of the platform theorem `LinearProgrammingBound`. The volume of the ball of radius $1/2$ is `MeasureTheory.volume.real (Metric.ball 0 (1/2))`, and the exponent is the real power `(2 : ℝ) ^ (-(0.599 - ε) * d)`, exactly as in `SpherePackingBeyond.kabatiansky_levenshtein`. The hypothesis $\widehat f(0) > 0$ is part of the conclusion (it rules out the degenerate quotient and gives $f \ne 0$). Restricting to Schwartz functions loses nothing: an admissible function with enough decay is turned into a Schwartz one (multiply by a wide Gaussian, convolve with $\varphi*\widetilde\varphi$ for a narrow Schwartz bump $\varphi$, rescale by $1+\delta$) at the cost of a factor $1+o(1)$ in the ratio, absorbed by $\varepsilon$.
-- source:
--   H. Cohn and Y. Zhao, Sphere packing bounds via spherical codes, Duke Math. J. 163 (2014), no. 10, 1965–2002 (the Cohn–Elkies linear programming bound is always at least as strong as the Kabatiansky–Levenshtein bound; analogue of Rodemich's theorem). G. A. Kabatiansky and V. I. Levenshtein, Bounds for packings on a sphere and in space, Problems Inform. Transmission 14 (1978), 1–17 (Δ_d ≤ 2^{-(0.5990…+o(1))d}). H. Cohn and N. Elkies, New upper bounds on sphere packings I, Ann. of Math. 157 (2003), 689–714, Theorem 3.1 (the linear programming bound; on the platform as LinearProgrammingBound). H. Cohn, A conceptual breakthrough in sphere packing, Notices AMS 64 (2017). Origin of this statement: it is the missing step of a reduction of SpherePackingBeyond.kabatiansky_levenshtein (Δ_d ≤ 2^{-(0.599-ε)d} for all large d). In that reduction everything else is proved in Lean: a unit packing of Def_TenChallenges_SpherePacking is turned into a SpherePacking of separation 2 with literally the same density (so spherePackingConstant d ≤ SpherePackingConstant d, axiom-free), and the platform theorem LinearProgrammingBound (Cohn–Elkies), rewritten in real numbers, bounds SpherePackingConstant d by the ratio in item 4.

import Mathlib

set_option autoImplicit false
open scoped FourierTransform SchwartzMap

namespace LefebvreVariations
theorem cohn_elkies_kabatiansky_levenshtein :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ),
        (∀ x, (((f x).re : ℝ) : ℂ) = f x) ∧
        (∀ x, (((𝓕 f x).re : ℝ) : ℂ) = 𝓕 f x) ∧
        (∀ x, 1 ≤ ‖x‖ → (f x).re ≤ 0) ∧
        (∀ x, 0 ≤ (𝓕 f x).re) ∧
        0 < (𝓕 f 0).re ∧
        (f 0).re / (𝓕 f 0).re *
            MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≤
          (2 : ℝ) ^ (-(0.599 - ε) * (d : ℝ)) := by sorry
end LefebvreVariations
