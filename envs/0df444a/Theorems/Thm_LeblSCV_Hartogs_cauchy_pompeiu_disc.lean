-- Prove2me | Theorems.Thm_LeblSCV_Hartogs_cauchy_pompeiu_disc
-- name    : LeblSCV.Hartogs.cauchy_pompeiu_disc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:37:29.405641+00:00
-- url     : https://prove2.me/theorems/7659e38e-30f5-4b74-b495-a0f0e5ec7164
-- title:
--   Theorem 4.1.1 — Cauchy–Pompeiu formula (on a disc)
-- statement:
--   Let $U = \{\zeta \in \mathbb{C} : |\zeta - c| < r\}$ be an open disc with $r > 0$, and let $f : \overline{U} \to \mathbb{C}$ be continuous, with continuous partial derivatives in $U$ that are bounded on $U$. Then for every $z \in U$ the function $\zeta \mapsto \frac{\partial f}{\partial \bar\zeta}(\zeta)/(\zeta - z)$ is integrable on $U$, and
--   $$f(z) = \frac{1}{2\pi i} \int_{\partial U} \frac{f(\zeta)}{\zeta - z}\, d\zeta + \frac{1}{2\pi i} \int_U \frac{\frac{\partial f}{\partial \bar\zeta}(\zeta)}{\zeta - z}\, d\zeta \wedge d\bar\zeta,$$
--   where $\partial U$ is the circle $|\zeta - c| = r$ oriented positively and $d\zeta \wedge d\bar\zeta = (-2i)\, dA$ with $dA$ the Lebesgue area measure.
--
--   This generalized Cauchy integral formula reduces to the usual one when $f$ is holomorphic, and is the tool with which the book solves $\partial\psi/\partial\bar z = g$ in one variable (Lemma 4.4.6) and the compactly supported $\bar\partial$-problem (Theorem 4.2.1).
--
--   **Formalization Note.** Restriction: the book states the theorem for any bounded open set with piecewise-$C^1$ boundary; here $U$ is a disc, because Mathlib has no boundary integral over a general piecewise-$C^1$ domain. The boundary integral is Mathlib's `circleIntegral` (positively oriented), the area integral is the Bochner integral for `volume` on `ℂ` (the Lebesgue measure identified with $dx\,dy$), multiplied by $-2i$. "Continuous partial derivatives in $U$" is `ContDiffOn ℝ 1 f U`, and "bounded" is a uniform bound on the real derivative `fderiv ℝ f` over $U$ (equivalent to bounded $\partial f/\partial x$, $\partial f/\partial y$). The integrability of the area integrand (Exercise 4.1.1) is stated as part of the conclusion, so the Bochner integral cannot silently be $0$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 130, Theorem 4.1.1

import Mathlib
import Definitions.Def_LeblSCV_Shared_dbar

open Complex MeasureTheory
open scoped Real

namespace LeblSCV.Hartogs

/-- Theorem 4.1.1 (Cauchy–Pompeiu, Lebl, p. 130), for `U` an open disc `{|ζ - c| < r}`, `r > 0`.
Let `f` be continuous on the closed disc `Ū` with bounded continuous partial derivatives in `U`.
Then for `z ∈ U` the function `(∂f/∂ζ̄)(ζ)/(ζ - z)` is integrable on `U` and
`f(z) = (1/2πi) ∫_{∂U} f(ζ)/(ζ - z) dζ + (1/2πi) ∫_U (∂f/∂ζ̄)(ζ)/(ζ - z) dζ ∧ dζ̄`,
where `∂U` is the positively oriented circle and `dζ ∧ dζ̄ = (-2i) dA` (p. 130), `dA` the Lebesgue
area measure on `ℂ`. "Continuous partial derivatives in `U`" is `ContDiffOn ℝ 1 f U`; "bounded"
is a uniform bound on the real derivative `fderiv ℝ f ζ` over `U`. -/
theorem cauchy_pompeiu_disc {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hcont : ContinuousOn f (Metric.closedBall c r))
    (hC1 : ContDiffOn ℝ 1 f (Metric.ball c r))
    (hbdd : ∃ M : ℝ, ∀ ζ ∈ Metric.ball c r, ‖fderiv ℝ f ζ‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.ball c r) :
    IntegrableOn (fun ζ : ℂ => LeblSCV.Shared.dbar f ζ / (ζ - z)) (Metric.ball c r) ∧
      f z = (2 * π * I)⁻¹ * (∮ ζ in C(c, r), f ζ / (ζ - z)) +
        (2 * π * I)⁻¹ * ((-2 * I) * ∫ ζ in Metric.ball c r, LeblSCV.Shared.dbar f ζ / (ζ - z)) := by sorry

end LeblSCV.Hartogs
