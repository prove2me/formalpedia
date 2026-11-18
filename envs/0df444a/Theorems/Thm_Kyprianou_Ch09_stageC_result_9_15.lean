-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_15
-- name    : Kyprianou.Ch09.stageC_result_9_15
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:45:41.378515+00:00
-- url     : https://prove2.me/theorems/12d75980-5f52-479d-9b61-ce59a4b674a7
-- title:
--   Result 9.15: Strict comparison in low-penalty stopping game
-- statement:
--   Result 9.15. Model and parameter assumptions: Theorem 9.14(b) low-penalty regime with repaired δcrit, unique z*∈(x*,logK), and candidate v*. Quantifiers and stopping-time domain: Every x<logK and any positive δ satisfying 0<δ<δcrit. Mathematical assertion: The function v* from the proof of Theorem 9.14(b) is strictly greater than δ for all x<log K. Endpoint and source qualification: Same as printed under correctly partitioned regime; prove via q-perturbed McKean values and limiting argument. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.15; original PDF pp. [275]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceGame
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_15 :
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (ψ : ℝ → ℝ)
    (d : ℝ) (S : ℝ≥0 → Ω → ℝ) (jumpMeasure : Measure ℝ)
    (K δ : ℝ) (W : ℝ → ℝ)
    (hX : B1.SourceModel P X F)
    (hBV : B1.IsBVNegativeLevy P X ψ d S jumpMeasure)
    (hJump : jumpMeasure ≠ 0)
    (hMean : Integrable (fun ω => S 1 ω) P)
    (hDrift : 0 < (∫ ω, S 1 ω ∂P) ∧
      (∫ ω, S 1 ω ∂P) < d)
    (hPsi : 0 < ψ 1) (hK : 0 < K) (hδ : 0 < δ)
    (hW : B1.IsScale ψ 0 W),
    let ψprime := d - (∫ ω, S 1 ω ∂P)
    let zMcKean := B1.gameLowerBarrier K ψprime (ψ 1)
    let critical := B1.gameCriticalPenalty K ψprime (ψ 1) W
    δ < critical →
      ∀ z : ℝ, zMcKean < z → z < Real.log K →
        B1.gamePenaltyAt K (ψ 1) z W = δ →
        ∀ x : ℝ, x < Real.log K →
          δ < B1.putLowPenaltyValue K (ψ 1) z δ x W := by
  sorry

end Kyprianou.Ch09
