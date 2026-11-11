-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_proposition_A_2
-- name    : LogSupermodularBIS.Main.proposition_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:34.991565+00:00
-- url     : https://prove2.me/theorems/454cfdf3-f971-4712-a66a-2953f974a11d
-- title:
--   Proposition A.2 — relative counting from residual samplers
-- statement:
--   Suppose that the residual law of every node can be sampled within total variation distance $\eta$, for every $0<\eta\le1/2$, at cost $C_s\,\mathrm{poly}(d,\log(1/\eta))$ on every execution. Then relative counting of $Z_W$ with error $0<\epsilon\le1/2$ and failure probability $0<\delta\le1/2$ costs
--   $$(C_s+T_W)\,\mathrm{poly}(d,\epsilon^{-1},\log(1/\delta))$$
--   on every execution: the counter returns $\widehat Z$ with $\Pr[|\widehat Z/Z_W-1|\le\epsilon]\ge1-\delta$.
--
--   Precisely: for every degree $a_0$ there are absolute $C>0$, $a\in\mathbb N$ such that every admissible sampler program yields an admissible counter, chosen before $d,B,T_W,W,C_s$ and the sampler's parameters, with cost $C(C_s+T_W)(1+d+1/\epsilon+\log(1/\delta))^a$. The counter receives $\epsilon,\delta$ and then the sampler's parameters. Log-supermodularity is not assumed.
--
--   Differences from the source:
--   - encoding: a sampler of every residual law within η at cost C_s poly(d, log(1/η)) → a program S with IsResidualSampler (cost C_s(1+d+log(1/η))^{a₀}); C, a chosen after a₀, the counter after S; reason: the polynomial’s own constant is absorbed in C_s
--   - encoding: a randomized algorithm in the exact real-arithmetic model with an O(·)/poly(·) running time on every execution → an existential Admissible program of the costed real RAM (rational literals; unit-cost arithmetic, comparisons, log, exp, uniform (0,1) draws; T_W per weight evaluation), chosen before all inputs, with a bound C·exp(C·X)·(1+params)^a on every tape in (0,1)^ℕ, C>0 and a∈ℕ absolute; reason: makes the uniform algorithm, the charged cost and the absolute constants of O(·) and poly(·) explicit; no instance is excluded
--   - encoding: an exact evaluator using at most T_W operations per value → an evaluator instruction charged T_W operations, with T_W ≥ 1, not given to the program; reason: an evaluation that returns a value costs at least one operation; the evaluator is accessed only through this instruction
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 39 (PDF 40), Proposition A.2

import Definitions.Def_LogSupermodularBIS_Main_Algorithms

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Proposition A.2 (Counting from the sampler), p. 39. For every polynomial degree `a₀` of the
sampler's cost there are absolute constants `C, a` such that every residual sampler program `S`
yields a relative counter of `Z_W` with cost `C (C_s + T_W)(1 + d + ε⁻¹ + log(1/δ))^a` on every
execution. The counter receives `ε, δ` and then the sampler's parameters `par`. -/
theorem proposition_A_2 :
    ∀ a₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ S : Program, Admissible S →
      ∃ Cnt : Program, Admissible Cnt ∧
        ∀ (d B TW : ℕ) (W : (Fin d → Bool) → ℚ), StandingWeight W B → 1 ≤ TW →
        ∀ (par : List ℝ) (Cs : ℝ), IsResidualSampler S W TW B par Cs a₀ →
        ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
          CountsWithin Cnt (evaluator W TW) (counterInput d B ε δ par) (partitionFn W) ε δ
            (C * (Cs + TW) * (1 + d + 1 / ε + Real.log (1 / δ)) ^ a) := by sorry

end LogSupermodularBIS.Main
