-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_theorem_1_2
-- name    : LogSupermodularBIS.Main.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:24.628319+00:00
-- url     : https://prove2.me/theorems/cf05991f-7b2b-4274-a470-eea2a947cd49
-- title:
--   Theorem 1.2 — counting and sampling with log-supermodular weights
-- statement:
--   Let $W:\{0,1\}^d\to\mathbb Q_{>0}$, $d\ge2$, be log-supermodular, given by an exact evaluator using at most $T_W$ operations per value, with every value of bit length at most $B\ge1$; the algorithms receive $d$ and $B$. There are randomized algorithms with the following guarantees.
--   1. For every real $0<\eta\le1/2$, the sampling algorithm returns a configuration whose law is within total variation distance $\eta$ of $\mu_W$. Its running time is at most
--   $$\exp\Bigl(O\bigl(\min\{d,\ d^{1/3}\log^{2/3}d\,\log^{2/3}(d+B)\}\bigr)\Bigr)\,\mathrm{poly}(d,B,T_W,\log(1/\eta)).$$
--   2. For all reals $\epsilon,\delta\in(0,1/2]$, the counting algorithm returns an estimate $\widehat Z$ satisfying $\Pr[|\widehat Z/Z_W-1|\le\epsilon]\ge1-\delta$. Its running time is at most
--   $$\exp\Bigl(O\bigl(\min\{d,\ d^{1/3}\log^{2/3}d\,\log^{2/3}(d+B)\}\bigr)\Bigr)\,\mathrm{poly}(d,B,T_W,\epsilon^{-1},\log(1/\delta)).$$
--
--   Both bounds hold on every execution in the exact real-arithmetic model. The two programs and the constants are chosen before $d$, $B$, $T_W$ and $W$.
--
--   Differences from the source:
--   - encoding: a randomized algorithm in the exact real-arithmetic model with an O(·)/poly(·) running time on every execution → an existential Admissible program of the costed real RAM (rational literals; unit-cost arithmetic, comparisons, log, exp, uniform (0,1) draws; T_W per weight evaluation), chosen before all inputs, with a bound C·exp(C·X)·(1+params)^a on every tape in (0,1)^ℕ, C>0 and a∈ℕ absolute; reason: makes the uniform algorithm, the charged cost and the absolute constants of O(·) and poly(·) explicit; no instance is excluded
--   - encoding: an exact evaluator using at most T_W operations per value → an evaluator instruction charged T_W operations, with T_W ≥ 1, not given to the program; reason: an evaluation that returns a value costs at least one operation; the evaluator is accessed only through this instruction
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 3 (PDF 4), Theorem 1.2

import Definitions.Def_LogSupermodularBIS_Main_Algorithms

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Theorem 1.2 (Log-supermodular weights), p. 3. The sampler receives `d, B` and `η`; the
counter receives `d, B` and `ε, δ`. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ S Cnt : Program, Admissible S ∧ Admissible Cnt ∧
      ∀ (d B TW : ℕ) (W : (Fin d → Bool) → ℚ), StandingWeight W B → 1 ≤ TW →
      LogSupermodular W →
        (∀ η ∈ Set.Ioc (0 : ℝ) (1 / 2),
          SamplesWithin S (evaluator W TW) (nodeInput d B [] η []) d (gibbsLaw W) η
            (C * Real.exp (C * min (d : ℝ)
                ((d : ℝ) ^ ((1 : ℝ) / 3) * Real.log d ^ ((2 : ℝ) / 3) *
                  Real.log (d + B) ^ ((2 : ℝ) / 3))) *
              (1 + d + B + TW + Real.log (1 / η)) ^ a)) ∧
        ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
          CountsWithin Cnt (evaluator W TW) (counterInput d B ε δ []) (partitionFn W) ε δ
            (C * Real.exp (C * min (d : ℝ)
                ((d : ℝ) ^ ((1 : ℝ) / 3) * Real.log d ^ ((2 : ℝ) / 3) *
                  Real.log (d + B) ^ ((2 : ℝ) / 3))) *
              (1 + d + B + TW + 1 / ε + Real.log (1 / δ)) ^ a) := by sorry

end LogSupermodularBIS.Main
