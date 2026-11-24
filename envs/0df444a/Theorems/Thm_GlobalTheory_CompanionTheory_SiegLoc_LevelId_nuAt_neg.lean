-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_nuAt_neg
-- name    : GlobalTheory.CompanionTheory.SiegLoc.LevelId.nuAt_neg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:13:22.656503+00:00
-- url     : https://prove2.me/theorems/a6a7303b-60a2-4b23-b797-39ff5b196230
-- title:
--   Level Id: nu At neg
-- statement:
--   The Level Id construction uses the nu At neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianRepCountFourierExpansion.lean#L99-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianRepCountFourierExpansion.lean#L99-L114

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.LevelId
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.SiegLoc.LevelId.nuAt_neg (ϖ : R) {n k : ℕ} (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :
    nuAt ϖ (-B) = nuAt ϖ B := by sorry
