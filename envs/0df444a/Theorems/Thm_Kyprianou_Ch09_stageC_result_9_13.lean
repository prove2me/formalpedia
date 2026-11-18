-- Prove2me | Theorems.Thm_Kyprianou_Ch09_stageC_result_9_13
-- name    : Kyprianou.Ch09.stageC_result_9_13
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T18:44:24.153283+00:00
-- url     : https://prove2.me/theorems/97b47631-4a38-425c-8c10-0b5aa9f89b77
-- title:
--   Result 9.13: Six-condition saddle-point verification lemma
-- statement:
--   Result 9.13. Model and parameter assumptions: G,H:ℝ→[0,∞) continuous, H>G everywhere, q≥0, ℱ-stopping times may include ∞; E_x[sup_(t≥0)e^(−qt)H(X_t)]<∞ and P_x(exists finite lim_(t→∞)e^(−qt)G(X_t))=1 for all x. Quantifiers and stopping-time domain: All x∈ℝ, τ,σ∈T and proposed τ*,σ*∈T; tie τ≤σ pays G, σ<τ pays H. Mathematical assertion: If (i) v*≥G, (ii) v*≤H, (iii) v*(X_τ*)=G(X_τ*) on τ*<∞, (iv) v*(X_σ*)=H(X_σ*) on σ*<∞, (v) discounted v* stopped at τ* right-continuous submartingale, and (vi) discounted v* stopped at σ* right-continuous supermartingale, then (v*,τ*,σ*) is a saddle solution of (9.30). Endpoint and source qualification: Same as printed with full six clauses; extended-game stopping and terminal payoff conventions explicit. All stopping, derivative and boundary cases are interpreted by the full formal Lean proposition; the process and filtration use the published completed natural filtration on a Type-0 sample space.
-- source:
--   Kyprianou (2006), Chapter 9, Theorem 9.13; original PDF pp. [270]. Original printed version and errata retained in source/semantic_adjudication_v5_v2.json.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_SourceVerification
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Kyprianou.Ch09

theorem stageC_result_9_13 :
  ∀ {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (G H vstar : ℝ → ℝ)
    (τstar σstar : ℝ → Ω → WithTop ℝ≥0)
    (terminalG terminalH : ℝ → Ω → ℝ)
    (hModel : B1.SourceModel P X F)
    (hq : 0 ≤ q) (hGH : B1.GamePayoffDomain G H)
    (hTerminalG : ∀ x, ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 =>
        Real.exp (-q * (t : ℝ)) * G (x + X t ω))
        atTop (nhds (terminalG x ω)))
    (hUpperIntegral : ∀ x : ℝ,
      Integrable (fun ω => sSup {z : ℝ | ∃ t : ℝ≥0,
        z = Real.exp (-q * (t : ℝ)) * H (x + X t ω)}) P)
    (hτ : ∀ x, B1.AdmissibleStop F (τstar x))
    (hσ : ∀ x, B1.AdmissibleStop F (σstar x))
    (hLower : ∀ x, G x ≤ vstar x)
    (hUpper : ∀ x, vstar x ≤ H x)
    (hMeetG : ∀ x, ∀ᵐ ω ∂P,
      (τstar x ω ≠ ⊤) →
      (∀ t : ℝ≥0, τstar x ω = (t : WithTop ℝ≥0) →
        vstar (x + X t ω) = G (x + X t ω)))
    (hMeetH : ∀ x, ∀ᵐ ω ∂P,
      (σstar x ω ≠ ⊤) →
      (∀ t : ℝ≥0, σstar x ω = (t : WithTop ℝ≥0) →
        vstar (x + X t ω) = H (x + X t ω)))
    (hSub : ∀ x : ℝ,
      Submartingale
        (B1.stoppedDiscountedValue X vstar q x (τstar x)) F P)
    (hSuper : ∀ x : ℝ,
      Supermartingale
        (B1.stoppedDiscountedValue X vstar q x (σstar x)) F P)
    (hRCtau : ∀ x : ℝ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 =>
          B1.stoppedDiscountedValue X vstar q x (τstar x) s ω)
        (Set.Ici t) t)
    (hRCsigma : ∀ x : ℝ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 =>
          B1.stoppedDiscountedValue X vstar q x (σstar x) s ω)
        (Set.Ici t) t),
    ∀ x : ℝ,
      B1.genericGameValue P F X G H q x (terminalG x) (terminalH x) =
        vstar x ∧
      (∀ τ σ : Ω → WithTop ℝ≥0,
        B1.AdmissibleStop F τ → B1.AdmissibleStop F σ →
        (∫ ω, B1.gameGain X G H q x
          (terminalG x) (terminalH x) τ (σstar x) ω ∂P) ≤
        (∫ ω, B1.gameGain X G H q x
          (terminalG x) (terminalH x) (τstar x) (σstar x) ω ∂P) ∧
        (∫ ω, B1.gameGain X G H q x
          (terminalG x) (terminalH x) (τstar x) (σstar x) ω ∂P) ≤
        (∫ ω, B1.gameGain X G H q x
          (terminalG x) (terminalH x) (τstar x) σ ω ∂P)) := by
  sorry

end Kyprianou.Ch09
