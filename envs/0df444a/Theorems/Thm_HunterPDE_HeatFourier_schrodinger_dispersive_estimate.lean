-- Prove2me | Theorems.Thm_HunterPDE_HeatFourier_schrodinger_dispersive_estimate
-- name    : HunterPDE.HeatFourier.schrodinger_dispersive_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:04:12.245401+00:00
-- url     : https://prove2.me/theorems/017e1be1-1e65-4c1f-9049-7d31125bc7b8
-- title:
--   Theorem 5.16 — Schrödinger dispersive estimates: L², L¹→L^∞ with (4π|t|)^{−n/2}, and (5.16) L^{p'}→Lᵖ
-- statement:
--   Let $f \in \mathcal S(\mathbb{R}^n;\mathbb{C})$ and let $u \in C^\infty(\mathbb{R};\mathcal S)$ be the solution of $iu_t = -\Delta u$, $u(0) = f$. Then for all $t \in \mathbb{R}$
--   $$\|u(t)\|_{L^2} \le \|f\|_{L^2}, \qquad \|u(t)\|_{L^\infty} \le \frac{1}{(4\pi|t|)^{n/2}}\,\|f\|_{L^1},$$
--   and for $2 < p < \infty$, with $p' = p/(p-1)$,
--   $$\|u(t)\|_{L^p} \le \frac{1}{(4\pi|t|)^{n(1/2-1/p)}}\,\|f\|_{L^{p'}}.$$
--   These dispersive decay estimates are the starting point for Strichartz estimates and for the local theory of nonlinear Schrödinger equations.
--
--   **Formalization Note.** Norms are `eLpNorm` in $[0,\infty]$ and the factors $1/(4\pi|t|)^{\dots}$ are divisions in $[0,\infty]$; at $t = 0$ the right-hand sides are $\infty$ unless $f = 0$, which is the book's reading of $1/0$. The exponent $p$ is a real number with $2 < p$, and $L^p$ is `eLpNorm … (ENNReal.ofReal p)`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 138–139, Theorem 5.16, Eq. (5.16)

import Mathlib
import Definitions.Def_HunterPDE_HeatFourier_SchwartzCurve

namespace HunterPDE.HeatFourier

open MeasureTheory
open scoped SchwartzMap ENNReal

/-- Hunter, *Notes on PDEs*, pp. 138–139, Theorem 5.16 (dispersive estimates): let `f ∈ 𝓢` and
`u ∈ C^∞(ℝ; 𝓢)` the solution of (5.13). Then for all `t ∈ ℝ`
`‖u(t)‖_{L²} ≤ ‖f‖_{L²}`, `‖u(t)‖_{L^∞} ≤ 1/(4π|t|)^{n/2} · ‖f‖_{L¹}`,
and for `2 < p < ∞`, with `p' = p/(p − 1)`, (5.16)
`‖u(t)‖_{Lᵖ} ≤ 1/(4π|t|)^{n(1/2 − 1/p)} · ‖f‖_{L^{p'}}`.
The factors `1/(4π|t|)^{…}` are written as division in `[0, ∞]`, so at `t = 0` (for `n ≥ 1`) the
right-hand sides are `∞` unless `f = 0`, the book's reading of `1/0`. -/
theorem schrodinger_dispersive_estimate (n : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hu : IsSchwartzSchrodingerSolution f u)
    (hsmooth : IsStrongSmoothOn u Set.univ) (t : ℝ) :
    eLpNorm (u t) 2 volume ≤ eLpNorm f 2 volume ∧
    eLpNorm (u t) ∞ volume ≤
      eLpNorm f 1 volume / ENNReal.ofReal ((4 * Real.pi * |t|) ^ ((n : ℝ) / 2)) ∧
    ∀ p : ℝ, 2 < p →
      eLpNorm (u t) (ENNReal.ofReal p) volume ≤
        eLpNorm f (ENNReal.ofReal (p / (p - 1))) volume /
          ENNReal.ofReal ((4 * Real.pi * |t|) ^ ((n : ℝ) * (1 / 2 - 1 / p))) := by sorry

end HunterPDE.HeatFourier
