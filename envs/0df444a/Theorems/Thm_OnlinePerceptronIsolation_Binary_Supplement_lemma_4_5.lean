-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_Supplement_lemma_4_5
-- name    : OnlinePerceptronIsolation.Binary.Supplement.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:13:32.456224+00:00
-- url     : https://prove2.me/theorems/fef635bd-f775-4ba8-a93a-7a52d3ecc62d
-- title:
--   Lemma 4.5 — uniform uniqueness bound for rectangles
-- statement:
--   There is an absolute constant $C>0$ such that for every $m,r\ge3$, every measurable $\phi:\mathbb R^m\to\{-1,+1\}$, and every rectangle $B\subseteq\mathbb R^m$, independent columns $Y_i\sim N(0,I_m)$ satisfy
--   $$\mathbb P(U_{\phi,B})\le C\left(\frac1m+\frac{(\log m)^{3/2}\log r+(\log m)^2}{\sqrt r}+\frac{\log m}{\sqrt r}\right).$$
--   The event says that the signs $z_i=\phi(Y_i)$ uniquely place the normalized score in $B$ among all signings. The same constant works for all dimensions, maps and rectangles, including empty, open and unbounded ones. This estimate is the rectangle-uniqueness input of Theorem 3.2.
--
--   Differences from the source:
--   - encoding: one-based sign cube and real coordinates → zero-based Fin indices and exact real-valued signs; reason: coordinate relabelling preserves all signings, scores and Hamming distances
--   - encoding: products of arbitrary real intervals → a Rectangle structure of order-connected coordinate sets with its product carrier; reason: every permitted endpoint convention, empty interval and unbounded interval is represented
--   - encoding: an absolute O constant multiplying the displayed three-term sum → one positive C quantified before m, r, phi and B; reason: this is the explicit uniformity asserted in the source
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma 4.5, printed p. 16, PDF p. 18; Eq. (4.34); proof printed pp. 23–24, PDF pp. 25–26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_RectangleUniqueness
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- Lemma 4.5, printed p.16 / PDF p.18: one absolute constant before all data. -/
theorem lemma_4_5 : ∃ C : ℝ, 0 < C ∧
    ∀ (m r : ℕ), 3 ≤ m → 3 ≤ r →
      ∀ (ϕ : (Fin m → ℝ) → ℝ), Measurable ϕ →
        (∀ y, ϕ y = 1 ∨ ϕ y = -1) → ∀ B : Rectangle m,
        (ABPOnline.gaussMat m r).real (rectangleUniquenessEvent ϕ B) ≤
          C * (1 / m +
            ((Real.log m) ^ (3 / 2 : ℝ) * Real.log r + (Real.log m) ^ 2) /
              Real.sqrt r + Real.log m / Real.sqrt r) := by sorry

end OnlinePerceptronIsolation.Binary.Supplement
