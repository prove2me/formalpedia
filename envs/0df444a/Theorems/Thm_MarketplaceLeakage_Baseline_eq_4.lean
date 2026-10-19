-- Prove2me | Theorems.Thm_MarketplaceLeakage_Baseline_eq_4
-- name    : MarketplaceLeakage.Baseline.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:34.319982+00:00
-- url     : https://prove2.me/theorems/44277a9b-9039-485a-b088-fc1d2a9973f6
-- title:
--   (4), p. 9 — for a fee f ≥ 0 the seller's unique optimal direct price is v − f/2 if f ≤ 2μ and v − μ if f ≥ 2μ
-- statement:
--   Consider the baseline leakage game with value $v$, marginal cost $c<v$, and switching costs uniform on $[0,\mu]$, $\mu>0$. Let $f\ge 0$ be the marketplace's per-transaction fee. Then a direct price $p_d$ maximizes the seller's profit
--   $$\pi_f(p_d)=(p_d-c)\,G(v-p_d)+(v-c-f)\,\bigl(1-G(v-p_d)\bigr)$$
--   over all $p_d\le v$ if and only if
--   $$p_d=p_d^*(f)=\begin{cases}v-\mu & \text{if } f\ge 2\mu,\\ v-\dfrac f2 & \text{if } f\le 2\mu.\end{cases}$$
--   In particular the seller's best response exists and is unique for every nonnegative fee.
--
--   This is the seller's best-response function of the baseline model: at moderate fees the seller undercuts the marketplace price $v$ by half the fee, and at high fees it prices low enough to divert every buyer to its direct channel.
--
--   **Formalization Note.** The paper prefaces (4) with "Assuming $f\le v-c$"; the display in fact needs $f\ge 0$ (for $f<0$ the formula $v-f/2$ exceeds $v$, and the optimum is $p_d=v$), and holds for every $f\ge 0$ whether or not $f\le v-c$. The statement is therefore posed for $f\ge 0$. The two branches agree at $f=2\mu$; Lean writes the first branch for $2\mu\le f$. The standing assumption $c<v$ is kept as a hypothesis.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89cc00…3c98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 9, display (4)

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting

namespace MarketplaceLeakage.Baseline

/-- (4), p. 9: for `μ > 0` and any fee `f ≥ 0`, the seller's profit-maximizing direct price is
unique and equals `v − μ` if `f ≥ 2μ` and `v − f/2` if `f ≤ 2μ` (the branches agree at
`f = 2μ`). The page's "Assuming f ≤ v − c" is replaced by `0 ≤ f`, which is what the display
needs (for `f < 0` the optimum is `p_d = v`). -/
theorem eq_4 (v c μ : ℝ) (hvc : c < v) (hμ : 0 < μ) (f : ℝ) (hf : 0 ≤ f) (pd : ℝ) :
    IsSOpt v c μ f pd ↔ pd = (if 2 * μ ≤ f then v - μ else v - f / 2) := by sorry

end MarketplaceLeakage.Baseline
