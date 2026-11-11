-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_theorem_2_2
-- name    : LogSupermodularBIS.Main.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:34.299628+00:00
-- url     : https://prove2.me/theorems/d23be313-6398-49d8-9639-76b104123d6e
-- title:
--   Theorem 2.2 — estimator from threshold smoothing
-- statement:
--   Let $W$ satisfy the assumptions of Theorem 1.2 and be log-supermodular, and let $0<w\le1/2$. For every node $v$ and every real $0<\delta\le1/2$, a randomized algorithm returns a real $A_v\in[0,d(1+2B)]$ such that
--   $$\Pr\Bigl[\log Z_{\Phi_v}-\Bigl(\frac{dw^2}4+\frac18\Bigr)\le A_v\le\log Z_{\Phi_v}\Bigr]\ge1-\delta.\tag{2.4}$$
--   Every execution uses at most
--   $$\exp\bigl(O(w^{-1}\log d\log(d+B))\bigr)\,\mathrm{poly}(d,B,T_W,\log(1/\delta))\tag{2.5}$$
--   operations and uniform draws. At leaves it returns $A_v=0$.
--
--   One program serves all $d,B,T_W,W,w$; it receives $d,B$, the node, $\delta$ and $w$.
--
--   Differences from the source:
--   - encoding: a randomized algorithm in the exact real-arithmetic model with an O(·)/poly(·) running time on every execution → an existential Admissible program of the costed real RAM (rational literals; unit-cost arithmetic, comparisons, log, exp, uniform (0,1) draws; T_W per weight evaluation), chosen before all inputs, with a bound C·exp(C·X)·(1+params)^a on every tape in (0,1)^ℕ, C>0 and a∈ℕ absolute; reason: makes the uniform algorithm, the charged cost and the absolute constants of O(·) and poly(·) explicit; no instance is excluded
--   - encoding: an exact evaluator using at most T_W operations per value → an evaluator instruction charged T_W operations, with T_W ≥ 1, not given to the program; reason: an evaluation that returns a value costs at least one operation; the evaluator is accessed only through this instruction
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 11 (PDF 12), Theorem 2.2, (2.4), (2.5)

import Definitions.Def_LogSupermodularBIS_Main_Algorithms

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Theorem 2.2 (Estimator from threshold smoothing), p. 11. One program, receiving `δ` and
then `w`. -/
theorem theorem_2_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ E : Program, Admissible E ∧
      ∀ (d B TW : ℕ) (W : (Fin d → Bool) → ℚ), StandingWeight W B → 1 ≤ TW →
      LogSupermodular W →
      ∀ w ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ v : List Bool, v.length ≤ d →
      ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
        (∀ ω, ValidTape ω →
          HaltsWithin E (evaluator W TW) ω (nodeInput d B v δ [w])
              (C * Real.exp (C * (w⁻¹ * Real.log d * Real.log (d + B))) *
                (1 + d + B + TW + Real.log (1 / δ)) ^ a) ∧
            outReal E (evaluator W TW) ω (nodeInput d B v δ [w]) ∈
              Set.Icc (0 : ℝ) (d * (1 + 2 * B)) ∧
            (v.length = d → outReal E (evaluator W TW) ω (nodeInput d B v δ [w]) = 0)) ∧
        ENNReal.ofReal (1 - δ) ≤ tapeLaw {ω |
          residualLogPartition W v - (d * w ^ 2 / 4 + 1 / 8) ≤
              outReal E (evaluator W TW) ω (nodeInput d B v δ [w]) ∧
            outReal E (evaluator W TW) ω (nodeInput d B v δ [w]) ≤
              residualLogPartition W v} := by sorry

end LogSupermodularBIS.Main
