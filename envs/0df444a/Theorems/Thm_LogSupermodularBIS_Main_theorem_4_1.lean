-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_theorem_4_1
-- name    : LogSupermodularBIS.Main.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:01.209211+00:00
-- url     : https://prove2.me/theorems/5f9bb557-f2cb-4c97-8d61-029d885dce86
-- title:
--   Theorem 4.1 — estimator from a guide
-- statement:
--   Let $W$ satisfy the assumptions of Theorem 1.2 and be log-supermodular, let $0\le D\le d$ be an integer and $b^*\ge0$. If (4.2) holds for every residual (every node with at least one free coordinate), then for every node $v$ and $0<\delta\le1/2$ a randomized algorithm returns $A_v\in[0,d(1+2B)]$ such that
--   $$\Pr\bigl[\log Z_{\Phi_v}-b^*-1/8\le A_v\le\log Z_{\Phi_v}\bigr]\ge1-\delta.$$
--   At leaves it returns $0$. Every execution costs at most
--   $$\exp\bigl(O((D+1)\log d)\bigr)\,\mathrm{poly}(d,B,T_W,\log(1/\delta))\tag{4.3}$$
--   operations and uniform draws.
--
--   One program serves all $d,B,T_W,W,D,b^*$; it receives $d,B$, the node, $\delta$ and $D$ (but not $b^*$ or the witness).
--
--   Differences from the source:
--   - encoding: a randomized algorithm in the exact real-arithmetic model with an O(·)/poly(·) running time on every execution → an existential Admissible program of the costed real RAM (rational literals; unit-cost arithmetic, comparisons, log, exp, uniform (0,1) draws; T_W per weight evaluation), chosen before all inputs, with a bound C·exp(C·X)·(1+params)^a on every tape in (0,1)^ℕ, C>0 and a∈ℕ absolute; reason: makes the uniform algorithm, the charged cost and the absolute constants of O(·) and poly(·) explicit; no instance is excluded
--   - encoding: an exact evaluator using at most T_W operations per value → an evaluator instruction charged T_W operations, with T_W ≥ 1, not given to the program; reason: an evaluation that returns a value costs at least one operation; the evaluator is accessed only through this instruction
--   - reading: b* is a known bound and the algorithm is stated after the hypothesis (4.2) → one program chosen before D and b*, receiving D but not b*; reason: the source leaves the algorithm's inputs implicit; its proof (p. 24) returns min{k(1+Λ), max{0, max_ρ(Ĵ^(ρ) − γ)}}, which never uses b*, so the stronger reading is the source's own algorithm
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), pp. 20–21 (PDF 21–22), Theorem 4.1, (4.3)

import Definitions.Def_LogSupermodularBIS_Main_Algorithms
import Definitions.Def_LogSupermodularBIS_Main_Interaction

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Theorem 4.1 (Estimator from a guide), pp. 20–21. One program, receiving `δ` and then `D`. -/
theorem theorem_4_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ E : Program, Admissible E ∧
      ∀ (d B TW : ℕ) (W : (Fin d → Bool) → ℚ), StandingWeight W B → 1 ≤ TW →
      LogSupermodular W →
      ∀ D : ℕ, D ≤ d → ∀ bstar : ℝ, 0 ≤ bstar →
      (∀ v : List Bool, v.length < d → WitnessAt W B D bstar v) →
      ∀ v : List Bool, v.length ≤ d → ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
        (∀ ω, ValidTape ω →
          HaltsWithin E (evaluator W TW) ω (nodeInput d B v δ [(D : ℝ)])
              (C * Real.exp (C * ((D + 1) * Real.log d)) *
                (1 + d + B + TW + Real.log (1 / δ)) ^ a) ∧
            outReal E (evaluator W TW) ω (nodeInput d B v δ [(D : ℝ)]) ∈
              Set.Icc (0 : ℝ) (d * (1 + 2 * B)) ∧
            (v.length = d → outReal E (evaluator W TW) ω (nodeInput d B v δ [(D : ℝ)]) = 0)) ∧
        ENNReal.ofReal (1 - δ) ≤ tapeLaw {ω |
          residualLogPartition W v - bstar - 1 / 8 ≤
              outReal E (evaluator W TW) ω (nodeInput d B v δ [(D : ℝ)]) ∧
            outReal E (evaluator W TW) ω (nodeInput d B v δ [(D : ℝ)]) ≤
              residualLogPartition W v} := by sorry

end LogSupermodularBIS.Main
