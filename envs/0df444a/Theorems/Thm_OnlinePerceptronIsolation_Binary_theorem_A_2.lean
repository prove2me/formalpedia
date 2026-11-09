-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_theorem_A_2
-- name    : OnlinePerceptronIsolation.Binary.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:31.552004+00:00
-- url     : https://prove2.me/theorems/cfa951b9-3dd2-440c-961a-ae8f75b686a2
-- title:
--   Theorem A.2 — Nazarov's inequality with the explicit coefficient
-- statement:
--   Let $m\ge1$ and let $Z\in\mathbb R^m$ be a Gaussian random vector with arbitrary mean and possibly singular covariance. Suppose $b_0>0$ and $\operatorname{Var}(Z_j)\ge b_0$ for every coordinate. For every $u\in\mathbb R^m$ and $\delta>0$,
--   $$\mathbb P(Z\in O_u\setminus O_{u+\delta\mathbf1_m})\le\frac{\delta}{\sqrt{b_0}}\bigl(\sqrt{2\log m}+2\bigr),\qquad O_u=\{x:x_j\ge u_j\ \forall j\}.$$
--   The coefficient is retained exactly, including dimensions one and two. No independence between the Gaussian coordinates, zero-mean assumption, or invertibility of the covariance matrix is required. This gives the precise anti-concentration statement used for orthant shells.
--
--   Differences from the source:
--   - encoding: an m-dimensional Gaussian random variable → HasGaussianLaw on a probability space with m positive and orthants Set.Ici; reason: this covers every Gaussian law, including singular covariance, and makes the positive-dimensional convention explicit
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Theorem A.2, Eq. (A.5), printed p.19, PDF p.21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- Theorem A.2, printed p.19 / PDF p.21. Arbitrary mean, possibly singular covariance,
all positive dimensions, and the exact displayed coefficient. -/
theorem theorem_A_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (m : ℕ) (hm : 0 < m)
    (Z : Ω → Fin m → ℝ) (hZ : HasGaussianLaw Z P)
    (b₀ : ℝ) (hb₀ : 0 < b₀)
    (hvar : ∀ j : Fin m, b₀ ≤ variance (fun ω => Z ω j) P)
    (u : Fin m → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    P.real {ω | Z ω ∈ Set.Ici u \ Set.Ici (fun j => u j + δ)} ≤
      (δ / Real.sqrt b₀) * (Real.sqrt (2 * Real.log m) + 2) := by sorry

end OnlinePerceptronIsolation.Binary
