-- Prove2me | Theorems.Thm_KingRockAsymp_Distribution_thm_2_6_display_lipschitz_bound
-- name    : KingRockAsymp.Distribution.thm_2_6_display_lipschitz_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:32.089279+00:00
-- url     : https://prove2.me/theorems/f360c7bb-aa51-476a-b153-60c59cb83473
-- title:
--   Proof of Theorem 2.6, display (pp. 8–9) — Lipschitz bound on solutions near the true one (cited from [12], Thm 4.1)
-- statement:
--   Let $Z$ be a separable Banach space and assume the analytical assumptions M.1–M.4 at $(z^*,x^*)$ for $f : Z \times \mathbb R^n \to \mathbb R^m$ and $N : \mathbb R^n \rightrightarrows \mathbb R^m$, and let $J(z) = \{x \mid 0 \in f(z,x) + N(x)\}$. Then there are a compact neighborhood $U$ of $x^*$ and a constant $\lambda \ge 0$ such that, for all $z$ in a neighborhood of $z^*$,
--   $$|x - x^*| \le \lambda \|z - z^*\| \qquad \text{for every } x \in U \cap J(z).$$
--
--   In the proof of Theorem 2.6 the paper uses this bound at $z = z^\nu$ in the form $\tau_\nu^{-1}|x^\nu - x^*| \le \lambda\tau_\nu^{-1}\|z^\nu - z^*\|$, which makes the rescaled solution errors tight; it cites the bound from [12], Theorem 4.1.
--
--   **Formalization Note** The printed display is the instance $z = z^\nu(\omega)$ of the deterministic bound stated here, with the common factor $\tau_\nu^{-1} > 0$ cancelled.
-- source:
--   King & Rockafellar, Asymptotic Theory for Solutions in Statistical Estimation and Stochastic Programming, Math. Oper. Res. 18(1) (1993), proof of Theorem 2.6, display, pp. 8–9 (authors' manuscript pagination); cited from [12], Theorem 4.1

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic

namespace KingRockAsymp.Distribution

open Set Filter Topology Metric MeasureTheory ProbabilityTheory

theorem thm_2_6_display_lipschitz_bound {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [CompleteSpace Z] [TopologicalSpace.SeparableSpace Z] {n m : ℕ}
    (f : Z → Rn n → Rn m) (N : Rn n → Set (Rn m)) (z₀ : Z) (x₀ : Rn n) (Dz : Z → Rn m)
    (hM : AnalyticalAssumptions f N z₀ x₀ Dz) :
    ∃ U : Set (Rn n), IsCompact U ∧ U ∈ 𝓝 x₀ ∧ ∃ lam : ℝ, 0 ≤ lam ∧
      ∀ᶠ z in 𝓝 z₀, ∀ x ∈ U ∩ solMap f N z, ‖x - x₀‖ ≤ lam * ‖z - z₀‖ := by sorry

end KingRockAsymp.Distribution
