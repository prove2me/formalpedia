-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_red_surj
-- name    : GlobalTheory.CompanionTheory.SiegLoc.LevelId.red_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:49.62021+00:00
-- url     : https://prove2.me/theorems/fdc911f6-bb86-49d8-a275-8681ccbb9c12
-- title:
--   Level Id: red surj
-- statement:
--   The Level Id construction uses the red surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianRepCountFourierExpansion.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianRepCountFourierExpansion.lean#L46-L51

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

theorem GlobalTheory.CompanionTheory.SiegLoc.LevelId.red_surj (ϖ : R) (k : ℕ) {a b : ℕ} :
    Function.Surjective (red ϖ k : Matrix (Fin a) (Fin b) R → _) := by sorry
