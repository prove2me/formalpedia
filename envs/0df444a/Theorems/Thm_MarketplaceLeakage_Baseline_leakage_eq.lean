-- Prove2me | Theorems.Thm_MarketplaceLeakage_Baseline_leakage_eq
-- name    : MarketplaceLeakage.Baseline.leakage_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:37.592342+00:00
-- url     : https://prove2.me/theorems/fb7c5cd7-e09d-4a2a-9dfe-9858586afcd3
-- title:
--   Proof of Proposition 1, p. 34 — the equilibrium extent of leakage is f*/(2μ) = min{1/2, (v − c)/(2μ)}
-- statement:
--   In the baseline leakage game (value $v$, cost $c<v$, switching costs uniform on $[0,\mu]$, $\mu>0$), let $(f^*,p_d^*)$ be any equilibrium outcome of the reduced game. Then the extent of leakage, the share $G(v-p_d^*)$ of buyers who buy directly, satisfies
--   $$G(v-p_d^*)=\frac{f^*}{2\mu}=\min\Bigl\{\frac12,\;\frac{v-c}{2\mu}\Bigr\}.$$
--
--   This gives the leakage in closed form: it equals $1/2$ while $\mu\le v-c$ and $(v-c)/(2\mu)$ beyond.
--
--   **Formalization Note.** The paper adds "This is initially constant, and then decreasing in $\mu$"; that comparative statement is part of the goal theorem (Proposition 1), stated there about equilibrium outcomes at two values of $\mu$. The standing assumptions $c<v$ and $\mu>0$ are hypotheses.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89cc00…3c98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 34, §8.2, Proof of Proposition 1 (last paragraph)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting

namespace MarketplaceLeakage.Baseline

/-- Proof of Proposition 1, p. 34: in every equilibrium outcome `(f, pd)` the extent of leakage
`G(v − pd)` equals `f/(2μ)` and equals `min {1/2, (v − c)/(2μ)}`. -/
theorem leakage_eq (v c μ : ℝ) (hvc : c < v) (hμ : 0 < μ) (f pd : ℝ) (h : IsEq v c μ f pd) :
    leakage v μ pd = f / (2 * μ) ∧ leakage v μ pd = min (1 / 2) ((v - c) / (2 * μ)) := by sorry

end MarketplaceLeakage.Baseline
