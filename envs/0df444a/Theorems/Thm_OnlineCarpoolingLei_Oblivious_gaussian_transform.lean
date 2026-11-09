-- Prove2me | Theorems.Thm_OnlineCarpoolingLei_Oblivious_gaussian_transform
-- name    : OnlineCarpoolingLei.Oblivious.gaussian_transform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:56.404788+00:00
-- url     : https://prove2.me/theorems/b6cde0ef-4095-489b-949e-1d1a755cfae7
-- title:
--   Lemma 5.2 — $\mathbb E\Psi_g(Z)\le\mathbb E g(Z)$ for $Z\sim N(0,100)$
-- statement:
--   Let $g:\mathbb R\to[0,\infty)$ be a finite convex function and $\Psi_g$ as in (5.1). For $Z\sim N(0,100)$,
--   $$\mathbb E\,\Psi_g(Z)\le\mathbb E\,g(Z).$$
--   No integrability of $g$ is assumed: both expectations are of nonnegative functions and may equal $+\infty$; when $\mathbb E\,g(Z)<\infty$ the inequality shows that $\Psi_g(Z)$ is integrable.
--
--   The variance $100$ is the variance of $\langle G,e\rangle$ for $G\sim N(0,50I_n)$ and an edge $e$. This is the one-dimensional core of the Gaussian integral inequality (6.1).
--
--   Differences from the source:
--   - encoding: expectations E Ψ_g(Z), E g(Z) of nonnegative functions → lower Lebesgue integrals of ENNReal.ofReal against gaussianReal 0 100; reason: values in [0,∞] as in the source, no Bochner default value on nonintegrable g
--   - encoding: finite convex g : R → [0,∞) → g : ℝ → ℝ with ∀ s, 0 ≤ g s and ConvexOn ℝ Set.univ g; reason: a real-valued function with nonnegative values is exactly a function into [0,∞)
--   - encoding: the minima defining F_g and κ_g in (5.1) → real sInf of the images of [z−2,z+2] and [−27,27]; reason: finite convex functions on R are continuous; these nonempty compact intervals give attained minima, with nonnegative values bounded below
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Lemma 5.2, p.11 (PDF p.11); standing assumption and (5.1) on p.10

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_OneDimTransform

open MeasureTheory ProbabilityTheory

namespace OnlineCarpoolingLei.Oblivious

/-- Lemma 5.2 (p.11). For a finite convex `g : ℝ → [0, ∞)` and `Z ∼ N(0, 100)`,
`E Ψ_g(Z) ≤ E g(Z)`, as an inequality of extended nonnegative expectations (both sides may be
`+∞`; if the right side is finite, so is the left). -/
theorem gaussian_transform (g : ℝ → ℝ) (hg_nonneg : ∀ s, 0 ≤ g s)
    (hg_convex : ConvexOn ℝ Set.univ g) :
    ∫⁻ z, ENNReal.ofReal (psi1 g z) ∂(gaussianReal 0 100) ≤
      ∫⁻ z, ENNReal.ofReal (g z) ∂(gaussianReal 0 100) := by sorry

end OnlineCarpoolingLei.Oblivious
