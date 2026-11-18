-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_1
-- name    : Kyprianou.Ch09.stageC_result_9_1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T15:22:22.066169+00:00
-- url     : https://prove2.me/theorems/c2c370fd-81f0-4307-92ea-e14aaac46055
-- title:
--   Result 9.1: Verification lemma for Lévy optimal stopping
-- statement:
--   Result 9.1. Model and parameter assumptions: X Lévy under the right-continuous completed natural filtration, q≥0, G:ℝ→[0,∞) measurable, v(x)<∞ for all x, and P_x(lim_(t→∞) e^(−qt)G(X_t)<∞)=1 for every x. Quantifiers and stopping-time domain: Every x∈ℝ and every admissible ℱ-stopping time T; candidate τ*∈T. Mathematical assertion: If v*(x)=E_x[e^(−qτ*)G(X_τ*)]≥G(x) and (e^(−qt)v*(X_t):t≥0) is a right-continuous supermartingale, (v*,τ*) solves v(x)=sup_(τ∈T)E_x[e^(−qτ)G(X_τ)]. Endpoint and source qualification: Same as printed, retaining finite/infinite-horizon terminal convention and integrability required for optional sampling. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.1; original PDF pp. [248]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceVerification
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_1 :
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (q : ℝ) (G : ℝ → ℝ)
    (vstar : ℝ → ℝ)
    (τstar : ℝ → Ω → WithTop ℝ≥0)
    (terminal : ℝ → Ω → ℝ)
    (hModel : B1.SourceModel P X F)
    (hq : 0 ≤ q) (hG : Measurable G)
    (hGpos : ∀ z, 0 ≤ G z)
    (hTerminal : ∀ x, ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 =>
        Real.exp (-q * (t : ℝ)) * G (x + X t ω))
        atTop (nhds (terminal x ω)))
    (hCandidate : ∀ x, B1.AdmissibleStop F (τstar x) ∧
      vstar x = ∫ ω, B1.stoppedGain X G q x
        (terminal x) (τstar x) ω ∂P)
    (hLower : ∀ x, G x ≤ vstar x)
    (hRC : B1.DiscountedRightContinuous P X q vstar)
    (hSuper : ∀ x : ℝ,
      Supermartingale
        (fun (t : ℝ≥0) ω => Real.exp (-q * (t : ℝ)) * vstar (x + X t ω)) F P),
    ∀ x : ℝ,
      B1.optionValue P F X G q x (terminal x) = vstar x := by
  sorry

end Kyprianou.Ch09
