-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobNz_exists_SB_integral_mul_char_eq_one
-- name    : GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:21.713257+00:00
-- url     : https://prove2.me/theorems/f0b0fe9a-e91e-4094-bdd5-12a88b219114
-- title:
--   Frob Nz: exists SB integral mul char eq one
-- statement:
--   The Frob Nz construction uses the exists SB integral mul char eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzBruhatCharacterIntegralOne.lean#L110-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzBruhatCharacterIntegralOne.lean#L110-L150

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobNz

theorem GlobalTheory.CompanionTheory.FrobNz.exists_SB_integral_mul_char_eq_one : ∀ (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ),
    Continuous (fun g => (χ g : ℂ)) → ∃ α : SB G, ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ = 1 := by sorry
