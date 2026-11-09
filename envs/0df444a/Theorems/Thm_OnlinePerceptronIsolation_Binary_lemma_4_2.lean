-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_lemma_4_2
-- name    : OnlinePerceptronIsolation.Binary.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:09.789507+00:00
-- url     : https://prove2.me/theorems/06534879-e191-41f2-8365-0b123e8606bf
-- title:
--   Lemma 4.2 — upper bound on uniqueness
-- statement:
--   There is an absolute constant $C>0$ such that for every $m,r\ge3$, every measurable $\phi:\mathbb R^m\to\{-1,+1\}$, and every $\theta\in\mathbb R^m$, independent $Y_i\sim N(0,I_m)$ satisfy
--   $$\mathbb P(U_{\phi,\theta})\le C\left(\frac1m+\frac{(\log m)^{3/2}\log r+(\log m)^2}{\sqrt r}+\frac{\log m}{\sqrt r}\right).$$
--   The event requires that $z_i=\phi(Y_i)$ is the unique feasible signing among all $2^r$ signings for $r^{-1/2}\sum_i z_iY_i\ge\theta$. The same $C$ works for all dimensions, sign maps and thresholds. This finite-size estimate is the uniqueness obstruction in the deterministic hardness theorem.
--
--   Differences from the source:
--   - encoding: one-based sign cube and coordinates → zero-based Fin indices and exact real-valued signs; reason: a bijection of coordinate labels preserves every signing and Hamming distance
--   - encoding: an absolute O constant multiplying the displayed sum → one positive C chosen before m, r, phi and theta; reason: this is the stated uniform meaning of the O notation
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Lemma 4.2, Eq. (4.18), printed p.14, PDF p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Uniqueness
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Lemma 4.2, printed p.14 / PDF p.16. One absolute constant precedes ALL data. -/
theorem lemma_4_2 : ∃ C : ℝ, 0 < C ∧
    ∀ (m r : ℕ), 3 ≤ m → 3 ≤ r →
      ∀ (ϕ : (Fin m → ℝ) → ℝ), Measurable ϕ →
        (∀ y, ϕ y = 1 ∨ ϕ y = -1) → ∀ θ : Fin m → ℝ,
        (ABPOnline.gaussMat m r).real (uniquenessEvent ϕ θ) ≤
          C * (1 / m +
            ((Real.log m) ^ (3 / 2 : ℝ) * Real.log r + (Real.log m) ^ 2) /
              Real.sqrt r + Real.log m / Real.sqrt r) := by sorry

end OnlinePerceptronIsolation.Binary
