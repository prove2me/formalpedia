-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobNz_exists_compact_open_subgroup_trivial
-- name    : GlobalTheory.CompanionTheory.FrobNz.exists_compact_open_subgroup_trivial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:26.227065+00:00
-- url     : https://prove2.me/theorems/a0549d6b-8b7e-4249-955b-a14eeb1c0291
-- title:
--   Frob Nz: exists compact open subgroup trivial
-- statement:
--   The Frob Nz construction uses the exists compact open subgroup trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzBruhatCharacterIntegralOne.lean#L44-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzBruhatCharacterIntegralOne.lean#L44-L108

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

theorem GlobalTheory.CompanionTheory.FrobNz.exists_compact_open_subgroup_trivial {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, χ k = 1 := by sorry
