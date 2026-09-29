-- Prove2me | Theorems.Thm_MeasureTheory_tendstoInMeasure_inv_sqrt_mul_of_dominated
-- name    : MeasureTheory.tendstoInMeasure_inv_sqrt_mul_of_dominated
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T22:15:37.18412+00:00
-- url     : https://prove2.me/theorems/dae75374-1d4b-4203-93a0-ecff10817501
-- title:
--   A sequence with a single dominating random variable is $o(\sqrt n)$ in probability
-- statement:
--   Let $(W_n)_{n\ge 0}$ be a sequence of real random variables on a finite measure space, and suppose there is a **single** measurable $Z$ dominating the whole sequence, $|W_n(\omega)| \le Z(\omega)$ for every $n$ and $\omega$. Then
--   $$\frac{W_n}{\sqrt n} \;\longrightarrow\; 0 \qquad \text{in probability.}$$
--
--   **Why this is the right hypothesis.** No integrability whatsoever is assumed: $Z$ need not be in $L^1$, let alone $L^2$. All that is used is that $Z$ is finite at every point. Indeed for fixed $\varepsilon>0$,
--   $$P\bigl(|W_n| \ge \varepsilon\sqrt n\bigr) \;\le\; P\bigl(Z \ge \varepsilon\sqrt n\bigr),$$
--   and the sets $\{Z \ge \varepsilon\sqrt n\}$ decrease to $\bigcap_n \{Z \ge \varepsilon \sqrt n\} = \emptyset$, since $Z(\omega)$ is a finite real number while $\varepsilon\sqrt n \to \infty$. Continuity of a finite measure from above finishes the proof. Finiteness of the measure is essential — it is what makes continuity from above available.
--
--   **Where it is used.** This is the standard "negligible remainder" step in central limit theorems for dependent sequences. In the Gordin–Maxwell–Woodroofe martingale approximation one writes a partial sum as a martingale plus a telescoping remainder,
--   $$\sum_{k<n} g(X_k) \;=\; \sum_{k<n} D_k \;+\; \hat g(X_0) - \hat g(X_n),$$
--   where $\hat g$ solves the Poisson equation $\hat g - P\hat g = g$. For a uniformly ergodic chain and bounded $g$ the solution $\hat g$ is bounded, so the remainder is dominated by the constant $2\|\hat g\|_\infty$; this lemma then says the remainder divided by $\sqrt n$ vanishes in probability, so it cannot affect the limit law. Taking $W_n \equiv Z$ recovers the familiar special case that a *fixed* random variable scaled by $n^{-1/2}$ tends to $0$ in probability.
-- source:
--   M. I. Gordin, "The central limit theorem for stationary processes", Soviet Math. Dokl. 10 (1969) 1174-1176; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Section 5.2; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem MeasureTheory.tendstoInMeasure_inv_sqrt_mul_of_dominated {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (W : ℕ → Ω → ℝ)
    (Z : Ω → ℝ) (hZ : Measurable Z) (hW : ∀ n ω, |W n ω| ≤ Z ω) :
    TendstoInMeasure P (fun (n : ℕ) (ω : Ω) => (Real.sqrt n)⁻¹ * W n ω) atTop 0 := by sorry
