-- Prove2me | Theorems.Thm_MDPFinance_JumpMarkets_theorem_9_3_6
-- name    : MDPFinance.JumpMarkets.theorem_9_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:28:31.927538+00:00
-- url     : https://prove2.me/theorems/e226de2e-2560-48c7-b5b8-63b4207d3e47
-- title:
--   Theorem 9.3.6 — investing everything in the bond is optimal iff E Y ≤ 0
-- statement:
--   **Theorem 9.3.6** (p. 289). If $U$ is continuously differentiable and $U'(x + u \cdot Y)Y$
--   is integrable for all $x > 0$ and $\|u\|$ small, then 'invest all the money in the bond' is optimal
--   if and only if $\mathbb{E}Y \le 0$.
--
--   A clean necessary-and-sufficient condition, with exactly the economic reading one wants: a
--   risk-averse investor has no incentive to hold a stock whose expected relative jump is not positive,
--   and — the converse, which is the harder half — as soon as some stock has a positive expected jump
--   it is worth holding a little of it.
--
--   **The theorem lives under the section's `Uncontrolled Drift` assumption, $\rho = \mu_i$ for all
--   $i$** (p. 289), i.e. the deterministic drift of every asset equals that of the bond. The planning
--   brief does not mention it, but the whole derivation on that page uses it: it is what reduces the
--   flow to $\phi^\alpha_t(x) = xe^{\rho t}$ and the fixed point equation to the pointwise form from
--   which the one-step-look-ahead comparison is read off. Without it the statement is not the book's.
--
--   **Both directions are the content.** The 'if' direction is the easy one — concavity of $U$ and
--   $\mathbb{E}Y \le 0$ give the one-step-look-ahead inequality
--   $\sup_u \mathbb{E}U(xe^{\rho(T-t-s)}(1+u\cdot Y)) \le U(xe^{\rho(T-t-s)})$ by Jensen. The 'only if'
--   is what the differentiability and integrability hypotheses are for. Stating one implication alone
--   would be a different, weaker theorem.
--
--   'Invest all the money in the bond' is the decision rule $f_* \equiv 0$, whose value function is
--   $J_{f_*}(t,x) = U(xe^{\rho(T-t)})$.
--
--   **Moderation note.** The draft's `V` was an arbitrary fixed point of `𝒯` (not the value function), and optimality was rendered as `f_* ∈ A^*_V`. Now the model is assumed contracting, `V` is the value function, optimality is `J_{f_*} = V`, and `U` is `C^1` on `(0,∞)` (the book's `x > 0`).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 289 (PDF 299), Theorem 9.3.6, under the Uncontrolled Drift assumption of the same page

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.JumpMarkets

/-- **Theorem 9.3.6** (p. 289), under the section's Uncontrolled Drift assumption `ρ = μ_i` for
all `i` and the standing contraction (`b_γ` bounding with `α_b < 1`). If `U` is continuously
differentiable (on `(0,∞)`) and `U'(x + u·Y)Y` is integrable for all `x > 0` and `‖u‖` small,
then 'invest all the money in the bond' (`f_* ≡ 0`) is optimal — `J_{f_*} = V` — if and only if
`𝔼Y ≤ 0`. -/
theorem theorem_9_3_6 {d : ℕ} (M : JumpMarket d)
    (huncontrolled : ∀ i : Fin d, M.mu i = M.rho)
    (gamma alpha : ℝ) (hb : M.IsBoundingFunction (M.bfun gamma) alpha) (halpha : alpha < 1)
    (hU1 : ContDiffOn ℝ 1 M.U (Set.Ioi 0))
    (hUint : ∀ x : ℝ, 0 < x → ∃ ε > (0 : ℝ), ∀ u : Fin d → ℝ, ‖u‖ < ε →
      ∀ i : Fin d, Integrable (fun y : Fin d → ℝ => deriv M.U (x + ∑ j, u j * y j) * y i) M.QY)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g))
    (bond : ℝ × ℝ → Control d)
    (hbond : ∀ p : ℝ × ℝ, (bond p).val = fun _ _ => 0) :
    ((∀ p ∈ M.E, M.Jstat Pr bond p = M.V Pr p) ↔ ∀ i : Fin d, ∫ y, y i ∂M.QY ≤ 0) := by sorry

end MDPFinance.JumpMarkets
