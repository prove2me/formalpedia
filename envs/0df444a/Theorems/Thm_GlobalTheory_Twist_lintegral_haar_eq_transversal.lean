-- Prove2me | Theorems.Thm_GlobalTheory_Twist_lintegral_haar_eq_transversal
-- name    : GlobalTheory.Twist.lintegral_haar_eq_transversal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:20.063392+00:00
-- url     : https://prove2.me/theorems/25ff8f7b-d05c-4a35-9a77-460bbe51d7bc
-- title:
--   Twist: lintegral haar eq transversal
-- statement:
--   The Twist construction uses the lintegral haar eq transversal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LintegralHaarEqCompactSubgroupTransversal.lean#L6-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LintegralHaarEqCompactSubgroupTransversal.lean#L6-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LintegralHaarEqCompactSubgroupTransversal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.Twist

theorem GlobalTheory.Twist.lintegral_haar_eq_transversal (G E : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace E] (μ mK : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
    [IsProbabilityMeasure mK] (lam : Measure E) [SFinite lam] (K : Set G) (e : E → G)
    (he : Measurable e) (hK : mK Kᶜ = 0)
    (hinv : ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK) (hlam : lam ≠ 0)
    (hfin : ∀ C : Set G, IsCompact C → lam {B | ∃ k ∈ K, k * e B ∈ C} < ⊤)
    (hact : ∀ g : G, ∃ ψ : E → E, Measurable ψ ∧ Measure.map ψ lam = lam ∧
      ∀ B, ∃ κ ∈ K, e B * g = κ * e (ψ B)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ENNReal, Measurable f →
      ∫⁻ g, f g ∂μ = ENNReal.ofReal c * ∫⁻ B, ∫⁻ k, f (k * e B) ∂mK ∂lam := by sorry
