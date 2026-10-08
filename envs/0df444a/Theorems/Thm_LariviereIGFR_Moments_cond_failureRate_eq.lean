-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_cond_failureRate_eq
-- name    : LariviereIGFR.Moments.cond_failureRate_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:32:16.86148+00:00
-- url     : https://prove2.me/theorems/2796fbbb-f79d-4464-ab24-e5185ff70703
-- title:
--   Proof of Theorem 2, p. 603 — X conditional on X > y has failure rate h_y(ξ) = h(ξ) for ξ > y
-- statement:
--   Let $X\ge 0$ have law $\mu$ with regular density $\phi$, failure rate $h$ and survival function $\bar\Phi$, and let $y$ satisfy $\bar\Phi(y)>0$. Let $X_y$ be $X$ conditional on $X>y$, with law $\mu(\,\cdot\mid X>y)$. Then $X_y$ has density
--   $$
--   \phi_y(s)=\begin{cases}\phi(s)/\bar\Phi(y), & s>y,\\ 0, & s\le y,\end{cases}
--   $$
--   and its failure rate $h_y=\phi_y/\bar\Phi_y$ satisfies
--   $$
--   h_y(\xi)=h(\xi)\qquad\text{for all }\xi>y.
--   $$
--
--   Conditioning on exceeding a level does not change the failure rate beyond that level; this lets the paper compare the tail $X_y$ with a Pareto law through $h$ alone.
--
--   **Formalization Note** The conditional law is Mathlib's `ProbabilityTheory.cond μ (Set.Ioi y)`, which is the zero measure when $\mu((y,\infty))=0$; the hypothesis $\bar\Phi(y)>0$ excludes that case. The density of $X_y$ is written out explicitly so that $h_y$ refers to a specific version.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §3, proof of Theorem 2, first paragraph

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 2, p. 603: `X_y`, the law of `X` conditional on `X > y`, has density
`ψ_y(s) = φ(s) / Φ̄(y)` for `s > y` (and `0` otherwise), and its failure rate equals `h` on `(y, ∞)`. -/
theorem cond_failureRate_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : LariviereIGFR.Char.IsRegDensity μ φ) (y : ℝ) (hy : 0 < LariviereIGFR.Char.survival μ y) :
    μ[|Set.Ioi y] = volume.withDensity
        (fun s => ENNReal.ofReal (if y < s then φ s / LariviereIGFR.Char.survival μ y else 0)) ∧
      ∀ ξ, y < ξ →
        LariviereIGFR.Char.failureRate (μ[|Set.Ioi y]) (fun s => if y < s then φ s / LariviereIGFR.Char.survival μ y else 0) ξ =
          LariviereIGFR.Char.failureRate μ φ ξ := by sorry

end LariviereIGFR.Moments
