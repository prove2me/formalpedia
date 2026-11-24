-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_exists_open_left_stab
-- name    : GlobalTheory.CompanionTheory.FrobHaarR.exists_open_left_stab
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:43:14.855974+00:00
-- url     : https://prove2.me/theorems/86fdc96e-b6eb-49f4-9216-4400c361bded
-- title:
--   Frob Haar R: exists open left stab
-- statement:
--   The Frob Haar R construction uses the exists open left stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L15-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalEqHaarMultiple.lean#L15-L49

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobHaarR
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.CompanionTheory.FrobHaarR.exists_open_left_stab {F : G → ℂ} (hF : F ∈ SB G) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, ∀ x, F (k * x) = F x := by sorry
