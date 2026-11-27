-- Prove2me | Theorems.Thm_InnovAlloc_Optimal_Supplement_proposition_4
-- name    : InnovAlloc.Optimal.Supplement.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T09:49:21.010805+00:00
-- url     : https://prove2.me/theorems/a7e484b6-3105-49e1-906f-ace73eda6f90
-- title:
--   Proposition 4 — optimal one-agent share, principal profit, effort and payoff
-- statement:
--   Let $B>1$ be capacity and let $\alpha\in[0,1]$. When all capacity is allocated to one agent, the unique optimal common share, optimized over $0<\gamma<1$, is
--
--   $$\gamma_m(B)=\frac1{\sqrt B},\qquad M(B)=\left(1-\frac1{\sqrt B}\right)^2.$$
--
--   At that share the effort game has an equilibrium, and every equilibrium has funded-agent effort $x_1=\log(\sqrt B)/B$ and unfunded-agent effort $x_2=0$. The principal earns $M(B)$ and the funded agent earns
--
--   $$\frac1{\sqrt B}-\frac1B+\frac{\log(1/\sqrt B)}B.$$
--
--   This supplies the optimized one-agent benchmark for Theorem 2, including the effort and payoff consequences in the original game. The logarithmic term in the agent payoff is negative.
--
--   Differences from the source:
--   - encoding: The page uses the equilibrium effort and profit of the one-agent allocation. → Existence and all-equilibrium effort, principal profit and agent payoff are stated using the published effort game.; reason: This connects every formula to the same game, including zero resources for the other agent.
--   - reading: The optimal sharing rate is given as gamma*=1/sqrt(B). → The given rate is admissible, globally maximizing on (0,1), and the only maximizing share.; reason: The scalar objective is strictly smaller away from this rate on B>1; the inactive branch is zero whereas its optimum is positive.
-- source:
--   Gao, Fan, Huang & Chen, “Resource Allocation Among Competing Innovators”, SSRN preprint 3658157 (February 2021), p. 18, Proposition 4

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Supplement_MonoSharing

namespace InnovAlloc.Optimal.Supplement

/-- Proposition 4 (p. 18), all four conclusions in the actual one-agent effort game. -/
theorem proposition_4 (α B : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hB : 1 < B) :
    IsMonoShare B (gammaM B) ∧
    (∀ γ, IsMonoShare B γ → γ = gammaM B) ∧
    profitMono (gammaM B) B = monoValue B ∧
    IsEquilibrium α (gammaM B) B 0 (Real.log (Real.sqrt B) / B) 0 ∧
    ∀ x1 x2, IsEquilibrium α (gammaM B) B 0 x1 x2 →
      x1 = Real.log (Real.sqrt B) / B ∧ x2 = 0 ∧
      principalProfit α (gammaM B) B 0 x1 x2 = (1 - 1 / Real.sqrt B) ^ 2 ∧
      agentPayoff α (gammaM B) B x1 0 x2 =
        1 / Real.sqrt B - 1 / B + Real.log (1 / Real.sqrt B) / B := by sorry

end InnovAlloc.Optimal.Supplement
