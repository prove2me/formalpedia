-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_proposition_2_1
-- name    : LogSupermodularBIS.Main.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:23.039253+00:00
-- url     : https://prove2.me/theorems/8a0f8b27-6c32-43a9-ba92-67e41988b590
-- title:
--   Proposition 2.1 — counting and sampling from coarse estimates
-- statement:
--   Suppose every residual admits the estimator in (2.3), with additive error bound $b\ge0$ and cost $C_0\,\mathrm{poly}(d,\log(1/\delta_{est}))$, $C_0\ge T_W$. For $\eta,\epsilon,\delta\in(0,1/2]$, every residual law can be sampled within total variation distance $\eta$ at cost
--   $$\exp(O(b+1))\,C_0\,\mathrm{poly}(d,\log(1/\eta)),$$
--   and $Z_W$ can be estimated within relative error $\epsilon$, with failure probability at most $\delta$, at cost
--   $$\exp(O(b+1))\,C_0\,\mathrm{poly}(d,\epsilon^{-1},\log(1/\delta)).$$
--   These bounds hold on every execution. No log-supermodularity is needed for this conversion.
--
--   The constants $C,a$ depend only on the estimator's polynomial degree $a_0$; the sampler and the counter depend only on the estimator program and receive $b$ and the estimator's parameters as inputs.
--
--   Differences from the source:
--   - encoding: an estimator with additive error b and cost C₀ poly(d, log(1/δ_est)) at every residual; known b → a program E with IsResidualEstimator (cost C₀(1+d+log(1/δ))^{a₀}); C, a chosen after a₀, the new program after E and before d, W, b, C₀; b and the estimator parameters passed as real inputs; reason: the polynomial’s own constant is absorbed in C₀; the conversion’s constants depend only on the estimator’s polynomial degree
--   - encoding: a randomized algorithm in the exact real-arithmetic model with an O(·)/poly(·) running time on every execution → an existential Admissible program of the costed real RAM (rational literals; unit-cost arithmetic, comparisons, log, exp, uniform (0,1) draws; T_W per weight evaluation), chosen before all inputs, with a bound C·exp(C·X)·(1+params)^a on every tape in (0,1)^ℕ, C>0 and a∈ℕ absolute; reason: makes the uniform algorithm, the charged cost and the absolute constants of O(·) and poly(·) explicit; no instance is excluded
--   - encoding: an exact evaluator using at most T_W operations per value → an evaluator instruction charged T_W operations, with T_W ≥ 1, not given to the program; reason: an evaluation that returns a value costs at least one operation; the evaluator is accessed only through this instruction
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 10 (PDF 11), Proposition 2.1

import Definitions.Def_LogSupermodularBIS_Main_Algorithms

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Proposition 2.1 (Counting and sampling from coarse estimates), p. 10. No log-supermodularity
is assumed. -/
theorem proposition_2_1 :
    ∀ a₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ E : Program, Admissible E →
      ∃ S Cnt : Program, Admissible S ∧ Admissible Cnt ∧
        ∀ (d B TW : ℕ) (W : (Fin d → Bool) → ℚ), StandingWeight W B → 1 ≤ TW →
        ∀ (par : List ℝ) (b C₀ : ℝ), 0 ≤ b → (TW : ℝ) ≤ C₀ →
          IsResidualEstimator E W TW B par b C₀ a₀ →
          IsResidualSampler S W TW B (b :: par) (C * Real.exp (C * (b + 1)) * C₀) a ∧
          ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
            CountsWithin Cnt (evaluator W TW) (counterInput d B ε δ (b :: par)) (partitionFn W)
              ε δ (C * Real.exp (C * (b + 1)) * C₀ * (1 + d + 1 / ε + Real.log (1 / δ)) ^ a) := by sorry

end LogSupermodularBIS.Main
