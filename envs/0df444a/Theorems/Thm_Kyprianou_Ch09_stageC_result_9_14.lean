-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_14
-- name    : Kyprianou.Ch09.stageC_result_9_14
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:45:04.687903+00:00
-- url     : https://prove2.me/theorems/1d7b3e0b-f526-4071-ad5d-6c049fae30d2
-- title:
--   Result 9.14: McKean stopping game and common penalty threshold
-- statement:
--   Result 9.14. Model and parameter assumptions: q=0, X spectrally negative bounded variation X_t=d t−S_t with d>E[S_1]>0 (hence a nonzero finite-mean negative-jump measure), ψ′(0+)=d−E[S_1]>0, ψ(1)>0, K>0, δ>0; G(x)=(K−e^x)⁺, H=G+δ, T allows ∞. Quantifiers and stopping-time domain: Every x∈ℝ; two regimes partition all δ>0 with equality in (a); source assumes E[S_1]>0, excluding pure upward drift. Mathematical assertion: Define δcrit=Kψ(1)∫_0^log(ψ(1)/ψ′(0+))e^(−y)W(y)dy=Kψ(1)∫_0^(logK−x*)e^(−y)W(y)dy. (a) δ≥δcrit, original McKean v(x)=K−e^x+ψ(1)e^x∫_0^(x−x*)e^(−y)W(y)dy, τ*=inf{t>0:X_t<x*}, σ*=∞. (b) 0<δ<δcrit, unique z*∈(x*,logK) via (9.42), v(x)=K−e^x+ψ(1)e^x∫_0^(x−z*)e^(−y)W(y)dy for x<logK, v=δ at x≥logK; τ*=inf{t>0:X_t<z*}, σ*=inf{t>0:X_t>logK}. Include strict-versus-weak boundaries and nonzero negative-jump measure as an inherited source hypothesis. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.14; original PDF pp. [272, 273]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceGame
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_14 :
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
    (0 ≤ critical) ∧
    (critical ≤ δ →
      ∀ x : ℝ,
        B1.penalisedPutGame P F X K δ x =
          B1.putGameCandidate K (ψ 1) zMcKean x W ∧
        B1.PutGameSaddle P F X K δ x
          (fun ω => B1.firstStrictBelow
            (fun t ξ => x + X t ξ) zMcKean ω)
          (fun _ => ⊤)) ∧
    (0 < δ ∧ δ < critical →
      ∃! z : ℝ,
        zMcKean < z ∧ z < Real.log K ∧
        B1.gamePenaltyAt K (ψ 1) z W = δ ∧
        (∀ x : ℝ,
          B1.penalisedPutGame P F X K δ x =
            B1.putLowPenaltyValue K (ψ 1) z δ x W ∧
          B1.PutGameSaddle P F X K δ x
            (fun ω => B1.firstStrictBelow
              (fun t ξ => x + X t ξ) z ω)
            (fun ω => B1.firstStrictAbove
              (fun t ξ => x + X t ξ) (Real.log K) ω))) := by
  sorry

end Kyprianou.Ch09
