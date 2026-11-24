-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_neg_mem_herm
-- name    : GlobalTheory.CompanionTheory.SiegLoc.LevelId.neg_mem_herm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:13:37.406003+00:00
-- url     : https://prove2.me/theorems/cbec7cf9-013e-40b5-856f-a8a87ccfd8d1
-- title:
--   Level Id: neg mem herm
-- statement:
--   The Level Id construction uses the neg mem herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianRepCountFourierExpansion.lean#L87-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianRepCountFourierExpansion.lean#L87-L97

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

theorem GlobalTheory.CompanionTheory.SiegLoc.LevelId.neg_mem_herm (σ : R →+* R) (ϖ : R) (n k : ℕ) {B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)}
    (hB : B ∈ hermMod σ ϖ n k) : -B ∈ hermMod σ ϖ n k := by sorry
