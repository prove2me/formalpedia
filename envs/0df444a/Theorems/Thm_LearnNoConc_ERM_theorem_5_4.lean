-- Prove2me | Theorems.Thm_LearnNoConc_ERM_theorem_5_4
-- name    : LearnNoConc.ERM.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:04.959028+00:00
-- url     : https://prove2.me/theorems/6a1be4fd-5d0c-4b99-b098-b67792dcbe7d
-- title:
--   Theorem 5.4, p. 21 — uniform empirical small-ball estimate on the L₂ unit sphere
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and let $H$ be a class of measurable functions on the unit sphere of $L_2(\mu)$ ($\|h\|_{L_2}=1$ for every $h\in H$). Let $X_1,\dots,X_N$ ($N\ge1$) be i.i.d. with law $\mu$ and $(\varepsilon_i)$ independent random signs. Suppose that $\tau>0$ satisfies $Q_H(2\tau)>0$, where $Q_H(u)=\inf_{h\in H}\Pr(|h|\ge u\|h\|_{L_2})$, and that
--
--   $$\mathbb E\sup_{h\in H}\Bigl|\frac1N\sum_{i=1}^N\varepsilon_i h(X_i)\Bigr|\le\frac{\tau Q_H(2\tau)}{16}.$$
--
--   Then, with probability at least $1-2\exp(-NQ_H^2(2\tau)/2)$,
--
--   $$\inf_{h\in H}\bigl|\{i:|h(X_i)|\ge\tau\}\bigr|\ge N\,\frac{Q_H(2\tau)}{4}.$$
--
--   This is the uniform lower estimate that drives the proof of Theorem 3.1: under a small-ball condition, every function of the class is large on a proportional number of sample points, without any concentration assumption.
--
--   **Formalization Note** The conclusion is stated as: the (outer) probability that some $h\in H$ has fewer than $NQ_H(2\tau)/4$ indices with $|h(X_i)|\ge\tau$ is at most $2\exp(-NQ_H^2(2\tau)/2)$. The expectation of the supremum is taken in $[0,\infty]$. Measurability of every $h$, membership in $L_2(\mu)$, and pointwise separability of $H$ (a countable subclass approximating every element pointwise and in $L_2$) are added; the last stands in for the measurability of suprema that the paper takes for granted.
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, Theorem 5.4, p. 21

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- Theorem 5.4, p. 21: the uniform empirical small-ball estimate on the `L₂(μ)` unit sphere. -/
theorem theorem_5_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Set (Ω → ℝ)) (hHm : ∀ h ∈ H, Measurable h) (hH2 : ∀ h ∈ H, MemLp h 2 μ)
    (hS : ∀ h ∈ H, eLpNorm h 2 μ = 1) (hHsep : PointwiseSeparable μ H)
    (N : ℕ) (hN : 0 < N) (τ : ℝ) (hτ : 0 < τ) (hQ : 0 < Q μ H (2 * τ))
    (hE : radSup μ H N ≤ ENNReal.ofReal (τ * Q μ H (2 * τ) / 16)) :
    (Measure.pi fun _ : Fin N => μ)
      {x | ∃ h ∈ H, ((Finset.univ.filter fun i => τ ≤ |h (x i)|).card : ℝ)
          < N * Q μ H (2 * τ) / 4}
      ≤ ENNReal.ofReal (2 * Real.exp (-(N * Q μ H (2 * τ) ^ 2 / 2))) := by sorry

end LearnNoConc.ERM
