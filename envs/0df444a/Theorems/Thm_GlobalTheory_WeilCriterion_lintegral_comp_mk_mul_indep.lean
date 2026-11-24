-- Prove2me | Theorems.Thm_GlobalTheory_WeilCriterion_lintegral_comp_mk_mul_indep
-- name    : GlobalTheory.WeilCriterion.lintegral_comp_mk_mul_indep
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:53:23.111379+00:00
-- url     : https://prove2.me/theorems/8790fab0-c750-4079-aa36-5275007f9f7f
-- title:
--   Weil Criterion: lintegral comp mk mul indep
-- statement:
--   The Weil Criterion construction uses the lintegral comp mk mul indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L108-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeilCriterionInvariantMeasureHomogeneousSpace.lean#L108-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H]
variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]

theorem GlobalTheory.WeilCriterion.lintegral_comp_mk_mul_indep
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h)
    (dg : Measure G) [dg.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    {φ ψ : G → ℝ≥0∞} (hφ : Measurable φ) (hφ1 : ∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1)
    (hψ : Measurable ψ) (hψ1 : ∀ g : G, ∫⁻ h : H, ψ (g * h) ∂ν = 1)
    {F : G ⧸ H → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F (g : G ⧸ H) * φ g ∂dg = ∫⁻ g, F (g : G ⧸ H) * ψ g ∂dg := by sorry
