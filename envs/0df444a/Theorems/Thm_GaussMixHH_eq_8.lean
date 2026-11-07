-- Prove2me | Theorems.Thm_GaussMixHH_eq_8
-- name    : GaussMixHH.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:34:10.314196+00:00
-- url     : https://prove2.me/theorems/32be988d-f81c-48c2-8052-b5b2f84001f2
-- title:
--   (8), p.27 — $\big|\tfrac1H\sum_t|\Phi_x(\theta_t)-\Phi_y(\theta_t)|^2-\mathbb E_{\mathrm{Unif}(I)}|\Phi_x-\Phi_y|^2\big|\le\Gamma^2/25$ for all grid vectors
-- statement:
--   There is a universal constant $C>0$ such that both parts hold.
--
--   1. *(Deterministic step.)* Let $U$ be a grid, $\theta_1,\dots,\theta_H$ frequencies, $I=[\theta_0,q]$ and $\Gamma>0$. If $\max_{u,v\in U}|\hat Q_{uv}-Q_{uv}|\le\Gamma^2/100$, then simultaneously for all grid probability vectors $x,y$,
--   $$\Big|\frac1H\sum_{t=1}^{H}|\Phi_x(\theta_t)-\Phi_y(\theta_t)|^2-\mathbb E_{\theta\sim\mathrm{Unif}(I)}\big[|\Phi_x(\theta)-\Phi_y(\theta)|^2\big]\Big|\le\Gamma^2/25.\tag{8}$$
--   2. *(Probabilistic step.)* Let $0<\theta_0<q\le1/2$, $U\subseteq[0,\infty)$ a grid with $M=|U|$, $\Gamma>0$, $0<\zeta<1$, and $H\ge C\Gamma^{-4}\log(CM/\zeta)$. If $\theta_1,\dots,\theta_H$ are i.i.d. uniform on $I$, then with probability at least $1-\zeta/3$, $\max_{u,v}|\hat Q_{uv}-Q_{uv}|\le\Gamma^2/100$.
--
--   Together they show that the sampled frequencies preserve average squared differences for all pairs of grid distributions at once, including the one the convex program selects.
--
--   **Formalization Note** "With probability at least $1-\zeta/3$" is a measurable subset of the event with that probability under the product of uniform laws on $I$.
--
--   Differences from the source:
--   - generalization: frequencies θ_t sampled from I, Γ = c√λe^{−CA}, the grid of the proof (deterministic step) → any frequencies, any Γ > 0, any grid; reason: the expansion as quadratic forms uses only ‖x − y‖₁ ≤ 2
--   - generalization: H = ⌈CΓ^{−4} log(CM/ζ)⌉, 0 < ζ < 1/3, the grid of the proof (probabilistic step) → every H ≥ CΓ^{−4} log(CM/ζ), 0 < ζ < 1, every grid of squared radii u ≥ 0; reason: more samples only help; the proof's values are a special case
--   - encoding: with probability at least 1 − ζ/3 → ∃ measurable E inside the event with 1 − ζ/3 ≤ P(E); reason: avoids outer measure
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 20, eq. (8), p.27 (PDF p.29); H = ⌈CΓ^-4 log(CM/ζ)⌉, Q_uv, Q̂_uv on the same page

import Mathlib
import Definitions.Def_GaussMixHH_GridFit

open MeasureTheory Complex

namespace GaussMixHH

/-- **(8)** (uniform control of the empirical average squared differences).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), proof of Theorem 20, eq. (8), p.27
(PDF p.29); `H = ⌈CΓ^{−4} log(CM/ζ)⌉`, `Q_uv` and `Q̂_uv` are on the same page.

"Each summand in Q̂_uv lies in [−1, 1]. Hoeffding's inequality and a union bound over the M² pairs
give, with probability at least 1 − ζ/3, max_{u,v} |Q̂_uv − Q_uv| ≤ Γ²/100. Expanding the squared
differences as quadratic forms and using ∥x − y∥₁ ≤ 2, we obtain simultaneously for all grid
probability vectors x, y,
|(1/H) Σ_{t=1}^{H} |Φ_x(θ_t) − Φ_y(θ_t)|² − E_{θ∼Unif(I)}[|Φ_x(θ) − Φ_y(θ)|²]| ≤ Γ²/25. (8)"

**Formalization Note.**
* Two parts under one universal `C`: (a) the deterministic step, for any grid, any frequencies
  `θ₁, …, θ_H` and any `Γ > 0` (generalization: the frequencies need not lie in `I`); (b) the
  probabilistic step, for `H` i.i.d. uniform frequencies on `I = [θ₀, q] ⊆ (0, 1/2]`, any grid of
  squared radii `u ≥ 0` with `M = |U|`, any `0 < Γ`, `0 < ζ < 1` and any `H ≥ CΓ^{−4} log(CM/ζ)`
  (the paper's `H` is the ceiling of this bound).
* "With probability at least `1 − ζ/3`" is a measurable subset of the event of probability at
  least `1 − ζ/3` under the product of uniform laws `unifI θ₀ q`. -/
theorem eq_8 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (n : ℕ) (G : Finset ℝ) (θ₀ q : ℝ) (H : ℕ) (θs : Fin H → ℝ) (Γ : ℝ), 0 < Γ →
        (∀ u ∈ G, ∀ v ∈ G, |Qhat n θs u v - Qmat n θ₀ q u v| ≤ Γ ^ 2 / 100) →
        ∀ x y : ℝ → ℝ, IsProbVec G x → IsProbVec G y →
          |empSqDiff n G θs x y - avgSqDiff n G θ₀ q x y| ≤ Γ ^ 2 / 25) ∧
      (∀ (n : ℕ) (G : Finset ℝ) (θ₀ q Γ ζ : ℝ) (H : ℕ),
        0 < θ₀ → θ₀ < q → q ≤ 1 / 2 → (↑G : Set ℝ) ⊆ Set.Ici 0 → 0 < Γ → 0 < ζ → ζ < 1 →
        C * (Γ ^ 4)⁻¹ * Real.log (C * G.card / ζ) ≤ H →
        ∃ E : Set (Fin H → ℝ), MeasurableSet E ∧
          E ⊆ {θs | ∀ u ∈ G, ∀ v ∈ G, |Qhat n θs u v - Qmat n θ₀ q u v| ≤ Γ ^ 2 / 100} ∧
          1 - ζ / 3 ≤ (Measure.pi (fun _ : Fin H => unifI θ₀ q) E).toReal) := by sorry

end GaussMixHH
