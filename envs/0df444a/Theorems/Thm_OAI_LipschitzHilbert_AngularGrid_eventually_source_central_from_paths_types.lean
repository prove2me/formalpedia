-- Prove2me | Theorems.Thm_OAI_LipschitzHilbert_AngularGrid_eventually_source_central_from_paths_types
-- name    : OAI.LipschitzHilbert.AngularGrid.eventually_source_central_from_paths_types
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T19:35:44.888829+00:00
-- url     : https://prove2.me/theorems/f642b404-2a65-449b-8f77-71c754d0db5f
-- title:
--   OAI.LipschitzHilbert.AngularGrid.eventually_source_central_from_paths_types: intermediate lemma from OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LipschitzHilbert.main` and `OAI.LipschitzHilbert.uniform_truncation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A uniform Hilbert transform estimate for Lipschitz directions (result family 083)*, OpenAI Math Release, September 25, 2026, result family 83, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.LipschitzHilbert.AngularGrid.eventually_source_central_from_paths_types` of [lean/OAI/Analysis/LipschitzHilbert/Trees/SourceTypeUniformCentral.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceTypeUniformCentral.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.LipschitzHilbert.AngularGrid`, with `open Set MeasureTheory Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem eventually_source_central_from_paths_types (q A B Pconst d m Q : ℝ)
--       (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pconst)
--       (hd : 0 ≤ d) (hm : 0 ≤ m) (hqm : 2*q+2 ≤ m) (hQ : 0 ≤ Q) :
--       ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
--       ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
--       ∀ (μ : Measure X) (g : AngularGrid) (tops : Finset τ)
--         (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ),
--         (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
--         (∀ t ∈ tops, Integrable (weight t) μ) → (∀ t, Measurable (weight t)) →
--       ∀ (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
--         (value : X → σ → EuclideanSpace ℂ κ),
--         (∀ s, Measurable (fun x => value x s)) →
--         (∀ s ∈ packets, assigned s ∈ tops) →
--         (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
--       ∀ (start Nmass Fmass : ℝ), 0 < Nmass → 0 < Fmass →
--         L/2 ≤ Real.log Nmass → Real.log Nmass ≤ 2*L →
--         (∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth) →
--       ∀ (good : Set X), MeasurableSet good →
--       ∀ [IsFiniteMeasure (μ.restrict good)], (μ.restrict good).real univ ≤ Fmass →
--         (∀ x ∈ good, (∑ t ∈ tops, weight t x) ≤ L^m*Nmass) →
--       let S := ∑ t ∈ tops, ∫ x, weight t x ∂μ
--       S ≤ L^m*Nmass^2*Fmass →
--       ∀ (hK : 0 < SourceParameters.blockCount L),
--       let K := SourceParameters.blockCount L
--       let p := Real.sqrt L
--       let alpha := 2+PhaseCombinatorics.phaseParameter D
--       let mu := PhaseCombinatorics.phaseMu D p
--       let a := mu/(K:ℝ)
--       let phase := fun (i : Fin K) (eta : Fin K → ℝ) (j : ℕ) =>
--         phaseTubePoint (Pi.single i mu) eta (ShiftedBlocks.tag hK j)
--       let cost := 1+(L^q)^p*(L^A+1)^(alpha-1)
--       (∀ (i : Fin K) eta x, x ∈ good → ∀ c,
--         ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
--           (value x) (phase i eta) a x 0 c‖ ≤
--           L^(2*q)*(1+Real.sqrt (∑ j, (eta j)^2))*g.mass tops slope precision cutoff weight 0 c x) →
--       ∀ (count : Fin K → ℕ) (bad : Fin K → (Fin K → ℝ) → τ → Set X),
--         (∀ i, ∀ t ∈ tops, ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint i (count i))) →
--       (∀ i eta, Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
--         (∀ x ∈ good, ∀ j ≤ count i, ∀ c,
--           ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
--             (value x) (phase i eta) a x (ShiftedBlocks.endpoint i j) c‖ ≤
--             L^q*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint i j) c x) ∧
--         (∀ x ∈ good, cost*(∑ t ∈ tops.filter (fun t => x ∈ bad i eta t), weight t x) ≤ 1/2) ∧
--         (∀ t ∈ tops, Integrable ((good\bad i eta t).indicator (fun x => weight t x*
--           g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
--             (phase i eta) a alpha p (L^A) i t (count i) x)) μ) ∧
--         (∀ t ∈ tops, (∫ x, (good\bad i eta t).indicator (fun x => weight t x*
--           g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
--             (phase i eta) a alpha p (L^A) i t (count i) x) x ∂μ) ≤
--           Pconst*L^B*cost*(∫ x, weight t x ∂μ))) →
--       let W := fun x => ∑ s ∈ packets,
--         ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
--           (stop s) (assigned s) a x:ℝ):ℂ) • value x s
--       IntegrableOn (fun x => ‖W x‖) good μ ∧
--         (∫ x in good, ‖W x‖ ∂μ) ≤ L^(-Q)*Nmass*Fmass
--   ```
--
--   **Definitions.** The statement is written with `OAI.LipschitzHilbert.AngularGrid`, `OAI.LipschitzHilbert.AngularGrid.eligible`, `OAI.LipschitzHilbert.AngularGrid.mass`, `OAI.LipschitzHilbert.AngularGrid.sourceActivePathValue`, `OAI.LipschitzHilbert.AngularGrid.sourceBoundaryCoefficient`, `OAI.LipschitzHilbert.AngularGrid.sourcePacketAmplitude`, `OAI.LipschitzHilbert.ShiftedBlocks.endpoint` and `OAI.LipschitzHilbert.SourceParameters.blockCount` (definitions bundle `OAIQ090A000` of this split); `OAI.LipschitzHilbert.phaseTubePoint`, `OAI.LipschitzHilbert.PhaseCombinatorics.phaseMu`, `OAI.LipschitzHilbert.PhaseCombinatorics.phaseParameter` and `OAI.LipschitzHilbert.ShiftedBlocks.tag` (definitions bundle `OAIQ090A001` of this split).
--
--   **Used by.** The proof of `OAI.LipschitzHilbert.PacketLatticeData.eventually_assigned_parent_central_gain` of this split imports it.
-- source:
--   OpenAI, A uniform Hilbert transform estimate for Lipschitz directions (result family 083), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 83; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-uniform-Hilbert-transform-estimate-for-Lipschitz-directions-September-25-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LipschitzHilbert/Trees/SourceTypeUniformCentral.lean (declaration OAI.LipschitzHilbert.AngularGrid.eventually_source_central_from_paths_types)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A000
import Definitions.Def_OAIQ090A001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
namespace AngularGrid
attribute [local instance] Classical.propDecidable

theorem eventually_source_central_from_paths_types (q A B Pconst d m Q : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pconst)
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hqm : 2*q+2 ≤ m) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ (τ σ X : Type*) (κ : Type) [MeasurableSpace X] [Fintype κ],
    ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
    ∀ (μ : Measure X) (g : AngularGrid) (tops : Finset τ)
      (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ),
      (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
      (∀ t ∈ tops, Integrable (weight t) μ) → (∀ t, Measurable (weight t)) →
    ∀ (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ),
      (∀ s, Measurable (fun x => value x s)) →
      (∀ s ∈ packets, assigned s ∈ tops) →
      (∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) →
    ∀ (start Nmass Fmass : ℝ), 0 < Nmass → 0 < Fmass →
      L/2 ≤ Real.log Nmass → Real.log Nmass ≤ 2*L →
      (∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth) →
    ∀ (good : Set X), MeasurableSet good →
    ∀ [IsFiniteMeasure (μ.restrict good)], (μ.restrict good).real univ ≤ Fmass →
      (∀ x ∈ good, (∑ t ∈ tops, weight t x) ≤ L^m*Nmass) →
    let S := ∑ t ∈ tops, ∫ x, weight t x ∂μ
    S ≤ L^m*Nmass^2*Fmass →
    ∀ (hK : 0 < SourceParameters.blockCount L),
    let K := SourceParameters.blockCount L
    let p := Real.sqrt L
    let alpha := 2+PhaseCombinatorics.phaseParameter D
    let mu := PhaseCombinatorics.phaseMu D p
    let a := mu/(K:ℝ)
    let phase := fun (i : Fin K) (eta : Fin K → ℝ) (j : ℕ) =>
      phaseTubePoint (Pi.single i mu) eta (ShiftedBlocks.tag hK j)
    let cost := 1+(L^q)^p*(L^A+1)^(alpha-1)
    (∀ (i : Fin K) eta x, x ∈ good → ∀ c,
      ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) (phase i eta) a x 0 c‖ ≤
        L^(2*q)*(1+Real.sqrt (∑ j, (eta j)^2))*g.mass tops slope precision cutoff weight 0 c x) →
    ∀ (count : Fin K → ℕ) (bad : Fin K → (Fin K → ℝ) → τ → Set X),
      (∀ i, ∀ t ∈ tops, ¬g.eligible cutoff (precision t) (ShiftedBlocks.endpoint i (count i))) →
    (∀ i eta, Real.sqrt (∑ j, (eta j)^2) ≤ L^2 →
      (∀ x ∈ good, ∀ j ≤ count i, ∀ c,
        ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          (value x) (phase i eta) a x (ShiftedBlocks.endpoint i j) c‖ ≤
          L^q*g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint i j) c x) ∧
      (∀ x ∈ good, cost*(∑ t ∈ tops.filter (fun t => x ∈ bad i eta t), weight t x) ≤ 1/2) ∧
      (∀ t ∈ tops, Integrable ((good\bad i eta t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          (phase i eta) a alpha p (L^A) i t (count i) x)) μ) ∧
      (∀ t ∈ tops, (∫ x, (good\bad i eta t).indicator (fun x => weight t x*
        g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
          (phase i eta) a alpha p (L^A) i t (count i) x) x ∂μ) ≤
        Pconst*L^B*cost*(∫ x, weight t x ∂μ))) →
    let W := fun x => ∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x:ℝ):ℂ) • value x s
    IntegrableOn (fun x => ‖W x‖) good μ ∧
      (∫ x in good, ‖W x‖ ∂μ) ≤ L^(-Q)*Nmass*Fmass := by
  sorry

end AngularGrid
end LipschitzHilbert

end

end OAI
end
