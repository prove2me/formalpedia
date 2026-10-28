-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_canonical_supply_counts
-- name    : OAI.HardSphere.Groups.canonical_supply_counts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:51:00.240488+00:00
-- url     : https://prove2.me/theorems/7a55246a-336e-4898-a278-82eae7b6216a
-- title:
--   OAI.HardSphere.Groups.canonical_supply_counts: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped ENNReal NNReal BigOperators`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital`):
--
--   ```lean
--   theorem canonical_supply_counts {ell b Alo A H : ℝ}
--       (hell : 0<ell) (hb : 0<b) (hAlo : 0<Alo) (hA : 0<A) (hH : 0<H) :
--       ∃t₀ : ℝ,0<t₀ ∧ ∀t : ℝ,0<t → t≤t₀ →
--       ∃D₀ : ℝ,1≤D₀ ∧ ∀D α : ℝ,D₀≤D → Alo≤α → α≤A →
--       ∀(N K n : ℕ) [Nontrivial (Fin N)] (L : Length),50<L.val →
--       n=⌈t/(α/D)^2⌉₊ → ∀w : Time,t*(w:ℝ)=D⁻¹ →
--       ∀θ : ℝ,θ≤ell/6 → ∀v : Fin 3→Fin K,∀ω : ConfigurationPath N L,
--       Certificate (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
--         (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell θ H D (prefixTime midpointTime w) v ω →
--       let E := eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
--         (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω
--       ell*D/2≤(E.card:ℝ) ∧ 10*(E∩fullFailure n t (α/D) (D^(1/12:ℝ))
--         (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) w v ω).card≤E.card
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.Bridge.midpointTime`, `OAI.HardSphere.Groups.Certificate`, `OAI.HardSphere.Wiener.Time` and `OAI.HardSphere.Wiener.prefixTime` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Groups.eligibleList`, `OAI.HardSphere.Groups.fullFailure` and `OAI.HardSphere.PathCutoff.meanCost` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Length` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.Groups.physical_ground_bad_supply` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

theorem canonical_supply_counts {ell b Alo A H : ℝ}
    (hell : 0<ell) (hb : 0<b) (hAlo : 0<Alo) (hA : 0<A) (hH : 0<H) :
    ∃t₀ : ℝ,0<t₀ ∧ ∀t : ℝ,0<t → t≤t₀ →
    ∃D₀ : ℝ,1≤D₀ ∧ ∀D α : ℝ,D₀≤D → Alo≤α → α≤A →
    ∀(N K n : ℕ) [Nontrivial (Fin N)] (L : Length),50<L.val →
    n=⌈t/(α/D)^2⌉₊ → ∀w : Time,t*(w:ℝ)=D⁻¹ →
    ∀θ : ℝ,θ≤ell/6 → ∀v : Fin 3→Fin K,∀ω : ConfigurationPath N L,
    Certificate (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) ell θ H D (prefixTime midpointTime w) v ω →
    let E := eligibleList (n+n) (α/D) (D^(1/12:ℝ)) (64*(meanCost+1))
      (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (prefixTime midpointTime w) v ω
    ell*D/2≤(E.card:ℝ) ∧ 10*(E∩fullFailure n t (α/D) (D^(1/12:ℝ))
      (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) w v ω).card≤E.card := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
