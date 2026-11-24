-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobProd_exists_compact_clopen
-- name    : GlobalTheory.CompanionTheory.FrobProd.exists_compact_clopen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:46.419065+00:00
-- url     : https://prove2.me/theorems/7ae69788-a0f1-4829-9614-c2f4151e4253
-- title:
--   Frob Prod: exists compact clopen
-- statement:
--   The Frob Prod construction uses the exists compact clopen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzBruhatProdSpanTensors.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzBruhatProdSpanTensors.lean#L8-L15

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobProd

theorem GlobalTheory.CompanionTheory.FrobProd.exists_compact_clopen {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] {x : X} {u : Set X} (hu : IsOpen u) (hx : x ∈ u) :
    ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ x ∈ V ∧ V ⊆ u := by sorry
