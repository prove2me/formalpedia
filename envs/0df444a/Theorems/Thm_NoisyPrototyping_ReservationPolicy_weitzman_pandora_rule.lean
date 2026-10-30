-- Prove2me | Theorems.Thm_NoisyPrototyping_ReservationPolicy_weitzman_pandora_rule
-- name    : NoisyPrototyping.ReservationPolicy.weitzman_pandora_rule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:54.224379+00:00
-- url     : https://prove2.me/theorems/baa4b6a7-7230-4af0-a86c-d0184002492d
-- title:
--   Weitzman (1979), cited in the proof of Theorem 1, p. A2 (PDF 33) — Pandora's rule is optimal for the box problem with recall and outside option 0
-- statement:
--   Pandora's box problem $\hat{\mathcal P}$: there are $N$ boxes; box $i$ contains an independent value $X_i \sim G_i$, where $G_i$ is a probability distribution with finite mean, and opening it costs $w_i > 0$ and reveals $X_i$. The searcher opens boxes adaptively, in any order, may stop at any time, and then takes the value of one opened box or nothing (value $0$). Let $R_i$ be the smallest solution of
--   $$E[\max\{0, X_i - R\}] = w_i ,$$
--   and let $\sigma$ order the boxes so that $R_{\sigma(1)} \ge R_{\sigma(2)} \ge \cdots \ge R_{\sigma(N)}$. Pandora's rule opens boxes in the order $\sigma$, and after $n$ boxes stops as soon as $V_n = \max\{0, X_{\sigma(1)}, \dots, X_{\sigma(n)}\} \ge R_{\sigma(n+1)}$ (or $n = N$), taking the box attaining $V_n$ (nothing if every opened value is negative).
--
--   Then Pandora's rule is admissible, and its expected net payoff is at least that of every admissible adaptive policy.
--
--   This is the classical result the paper invokes once Claims 1 and 2 have reduced the noisy problem to $\hat{\mathcal P}$.
--
--   **Formalization Note** $\hat{\mathcal P}$ is `pandoraProblem G w`: the observed measurement of box $i$ equals its value. Pandora's rule is `fidelityPolicy` with $Q_i$ the identity. Ties between equal values go to the box opened later, the paper's rule for $B_n$.
-- source:
--   Bhaskaran and Erat, Optimal Prototyping with Noisy Measurements, author manuscript of 6 Nov 2024 (MSOM 2025, doi:10.1287/msom.2024.1133), p. A2 (PDF 33), proof of Theorem 1, citing Weitzman (1979), Optimal search for the best alternative, Econometrica 47(3):641–654

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model

namespace NoisyPrototyping.ReservationPolicy
open MeasureTheory
theorem weitzman_pandora_rule {N : ℕ} (G : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (G i)] (hG : ∀ i, Integrable (fun x : ℝ => x) (G i))
    (w : Fin N → ℝ) (hw : ∀ i, 0 < w i) (R : Fin N → ℝ)
    (hR : ∀ i, IsLeast {r : ℝ | ∫ x, max (x - r) 0 ∂(G i) = w i} (R i))
    (σ : Fin N ≃ Fin N) (hσ : ∀ a b, a ≤ b → R (σ b) ≤ R (σ a)) :
    Admissible (pandoraProblem G w) (fidelityPolicy (fun _ => id) σ R) ∧
    ∀ ρ : Policy N, Admissible (pandoraProblem G w) ρ →
      value (pandoraProblem G w) ρ ≤
        value (pandoraProblem G w) (fidelityPolicy (fun _ => id) σ R) := by sorry
end NoisyPrototyping.ReservationPolicy
