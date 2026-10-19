-- Prove2me | Theorems.Thm_MarketplaceLeakage_Baseline_optimal_fee
-- name    : MarketplaceLeakage.Baseline.optimal_fee
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:36.502484+00:00
-- url     : https://prove2.me/theorems/b8a74915-4cd6-4100-b51d-dac6a59f27f0
-- title:
--   Proof of Proposition 1, p. 34 — the marketplace's optimal fee is min{μ, v − c}
-- statement:
--   In the baseline leakage game (value $v$, cost $c<v$, switching costs uniform on $[0,\mu]$, $\mu>0$), a fee $f$ and a direct price $p_d$ form an equilibrium outcome of the reduced game — $f\le v-c$, $p_d$ is seller-optimal at $f$, and no feasible fee followed by a seller-optimal response gives the marketplace more — if and only if
--   $$f=\min\{\mu,\;v-c\}\quad\text{and}\quad p_d \text{ is seller-optimal at } f.$$
--
--   The unconstrained maximizer of $f(1-f/(2\mu))$ is $f=\mu$; the cap $f\le v-c$, beyond which the seller would not list, binds when $\mu>v-c$. This is the step of the proof of Proposition 1 that fixes the equilibrium fee.
--
--   **Formalization Note.** Negative fees are feasible in the marketplace's problem, as in (3) of the paper; the statement asserts that they are never chosen. The standing assumptions $c<v$ and $\mu>0$ are hypotheses.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89cc00…3c98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 34, §8.2, Proof of Proposition 1 (argmax display)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting

namespace MarketplaceLeakage.Baseline

/-- Proof of Proposition 1, p. 34: the marketplace's profit `f (1 − f/(2μ))` is maximized at
`f = μ`; with the constraint `f ≤ v − c`, a pair `(f, pd)` is an equilibrium outcome of the
reduced game exactly when `f = min {μ, v − c}` and `pd` is an optimal direct price at `f`. -/
theorem optimal_fee (v c μ : ℝ) (hvc : c < v) (hμ : 0 < μ) (f pd : ℝ) :
    IsEq v c μ f pd ↔ (f = min μ (v - c) ∧ IsSOpt v c μ f pd) := by sorry

end MarketplaceLeakage.Baseline
