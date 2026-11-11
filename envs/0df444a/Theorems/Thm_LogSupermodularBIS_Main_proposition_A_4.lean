-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_proposition_A_4
-- name    : LogSupermodularBIS.Main.proposition_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:44.46219+00:00
-- url     : https://prove2.me/theorems/65fa0466-83d9-404d-8e8b-834ffd69cb3d
-- title:
--   Proposition A.4 — sampling every residual from cached additive estimates
-- statement:
--   Assume the estimator guarantee (2.3) with additive error bound $b\ge0$ and cost $C_0\,\mathrm{poly}(d,\log(1/\delta_{est}))$, $C_0\ge T_W$, for a weight satisfying the standing assumptions (log-supermodularity is not assumed). Then for every $0<\eta\le1/2$ there is a sampler within total variation distance $\eta$ of $\mu_W$, and one within $\eta$ of the residual law $W_v/Z_v$ of every node $v$. Every execution uses at most
--   $$\exp(O(b+1))\,C_0\,\mathrm{poly}(d,\log(1/\eta))$$
--   operations and uniform draws.
--
--   Precisely: for every degree $a_0$ there are absolute constants $C>0$, $a\in\mathbb N$ such that every admissible estimator program $E$ yields an admissible sampler program $S$, chosen before $d,B,T_W,W,b,C_0$ and the estimator's parameters, with cost $Ce^{C(b+1)}C_0(1+d+\log(1/\eta))^a$ on every execution; the root residual is $\mu_W$. The sampler receives $\eta$, then $b$, then the estimator's parameters.
--
--   Differences from the source:
--   - encoding: an estimator with additive error b and cost C₀ poly(d, log(1/δ_est)) at every residual; known b → a program E with IsResidualEstimator (cost C₀(1+d+log(1/δ))^{a₀}); C, a chosen after a₀, the new program after E and before d, W, b, C₀; b and the estimator parameters passed as real inputs; reason: the polynomial’s own constant is absorbed in C₀; the conversion’s constants depend only on the estimator’s polynomial degree
--   - encoding: a randomized algorithm in the exact real-arithmetic model with an O(·)/poly(·) running time on every execution → an existential Admissible program of the costed real RAM (rational literals; unit-cost arithmetic, comparisons, log, exp, uniform (0,1) draws; T_W per weight evaluation), chosen before all inputs, with a bound C·exp(C·X)·(1+params)^a on every tape in (0,1)^ℕ, C>0 and a∈ℕ absolute; reason: makes the uniform algorithm, the charged cost and the absolute constants of O(·) and poly(·) explicit; no instance is excluded
--   - encoding: an exact evaluator using at most T_W operations per value → an evaluator instruction charged T_W operations, with T_W ≥ 1, not given to the program; reason: an evaluation that returns a value costs at least one operation; the evaluator is accessed only through this instruction
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 40 (PDF 41), Proposition A.4

import Definitions.Def_LogSupermodularBIS_Main_Algorithms

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Proposition A.4 (Sampling from additive estimates), p. 40. For every polynomial degree `a₀`
of the estimator's cost there are absolute constants `C, a` such that every estimator program `E`
satisfying (2.3) yields a residual sampler (the root residual is `μ_W`) with cost
`C e^{C(b+1)} C_0 (1 + d + log(1/η))^a` on every execution. The sampler receives `η` and then `b`
and the estimator's parameters `par`. -/
theorem proposition_A_4 :
    ∀ a₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ E : Program, Admissible E →
      ∃ S : Program, Admissible S ∧
        ∀ (d B TW : ℕ) (W : (Fin d → Bool) → ℚ), StandingWeight W B → 1 ≤ TW →
        ∀ (par : List ℝ) (b C₀ : ℝ), 0 ≤ b → (TW : ℝ) ≤ C₀ →
          IsResidualEstimator E W TW B par b C₀ a₀ →
          IsResidualSampler S W TW B (b :: par) (C * Real.exp (C * (b + 1)) * C₀) a := by sorry

end LogSupermodularBIS.Main
