-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_physical_group_common_comparison
-- name    : OAI.HardSphere.Groups.physical_group_common_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:56:18.731963+00:00
-- url     : https://prove2.me/theorems/253748a2-a1fd-4f6e-b35f-099fca43772d
-- title:
--   OAI.HardSphere.Groups.physical_group_common_comparison: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal BigOperators`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice`):
--
--   ```lean
--   theorem physical_group_common_comparison {N M G : ℕ} {L : Length}
--       (hL : L.val=(K:ℝ)) (hK : 1 ≤ K) (h50 : 50<L.val)
--       {ψ : Jet (N+1) L} {r : ℝ} (hψ : IsGroundVector (N+1) L r ψ)
--       (g : Fin G) (m : ℕ) (t R C S s₀ h : ℝ) (u : Time) (hs : PhysicalScaleBounds m t r R C S s₀ h u)
--       (hxy : x≠y) (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
--       (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
--       (hgood : ∀d∈E,ν d {p | simplePathGood (latticeDatumBad hL g m t r R C S u d) p}=1)
--       (hM : 0<M) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1 ≤ B) (hCpath : 0 ≤ Cpath)
--       (hBt : routeDensityBound t ≤ ENNReal.ofReal B)
--       (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ ≤ κ)
--       (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*datumCollisionBound t r h R C) ≤ 1)
--       (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d
--         ∂physicalDatumLaw g ψ m r R C S s₀ (2*t) u) ≤ ENNReal.ofReal Cpath) :
--       ∃σ : Measure (Torus L×Torus L×Configuration N L), IsFiniteMeasure σ ∧
--         σ univ=(physicalDatumLaw g ψ m r R C S s₀ (2*t) u) E ∧
--         ∀b,
--           let P := physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b
--           IsFiniteMeasure P ∧ σ≪P ∧ Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P ∧
--             (∫z,(σ.rnDeriv P z).toReal^2 ∂P) ≤ B*Cpath
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.Groups.GridAllocation`, `OAI.HardSphere.Groups.PhysicalDatum`, `OAI.HardSphere.Groups.PhysicalScaleBounds`, `OAI.HardSphere.Groups.routeDensityBound`, `OAI.HardSphere.Lattice.DiscreteTorus`, `OAI.HardSphere.Lattice.SimplePath`, `OAI.HardSphere.Lattice.simpleEncounter`, `OAI.HardSphere.Lattice.simplePathMeasurableSpace`, `OAI.HardSphere.Sampling.Allocation`, `OAI.HardSphere.Sampling.allocationMeasurable` and `OAI.HardSphere.Wiener.Time` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Groups.datumCollisionBound`, `OAI.HardSphere.Groups.latticeDatumBad`, `OAI.HardSphere.Groups.physicalDatumLaw`, `OAI.HardSphere.Groups.physicalGroupReference` and `OAI.HardSphere.Lattice.simplePathGood` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.IsGroundVector`, `OAI.HardSphere.Jet`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.condensation_with_mixed` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}

theorem physical_group_common_comparison {N M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1 ≤ K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} {r : ℝ} (hψ : IsGroundVector (N+1) L r ψ)
    (g : Fin G) (m : ℕ) (t R C S s₀ h : ℝ) (u : Time) (hs : PhysicalScaleBounds m t r R C S s₀ h u)
    (hxy : x≠y) (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (hgood : ∀d∈E,ν d {p | simplePathGood (latticeDatumBad hL g m t r R C S u d) p}=1)
    (hM : 0<M) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1 ≤ B) (hCpath : 0 ≤ Cpath)
    (hBt : routeDensityBound t ≤ ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ ≤ κ)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*datumCollisionBound t r h R C) ≤ 1)
    (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d
      ∂physicalDatumLaw g ψ m r R C S s₀ (2*t) u) ≤ ENNReal.ofReal Cpath) :
    ∃σ : Measure (Torus L×Torus L×Configuration N L), IsFiniteMeasure σ ∧
      σ univ=(physicalDatumLaw g ψ m r R C S s₀ (2*t) u) E ∧
      ∀b,
        let P := physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b
        IsFiniteMeasure P ∧ σ≪P ∧ Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P ∧
          (∫z,(σ.rnDeriv P z).toReal^2 ∂P) ≤ B*Cpath := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
