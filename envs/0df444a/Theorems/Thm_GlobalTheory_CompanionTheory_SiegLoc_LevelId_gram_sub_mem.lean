-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_LevelId_gram_sub_mem
-- name    : GlobalTheory.CompanionTheory.SiegLoc.LevelId.gram_sub_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:46.834381+00:00
-- url     : https://prove2.me/theorems/b538fce6-749a-4a38-92da-6158b869bd13
-- title:
--   Level Id: gram sub mem
-- statement:
--   The Level Id construction uses the gram sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianRepCountFourierExpansion.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianRepCountFourierExpansion.lean#L75-L85

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

theorem GlobalTheory.CompanionTheory.SiegLoc.LevelId.gram_sub_mem (σ : R →+* R) (ϖ : R) (hinv : ∀ a, σ (σ a) = a) (h : σ ϖ = ϖ) (k : ℕ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (hS : cT σ S = S) (hT : cT σ T = T)
    (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :
    cT (barσ σ ϖ h k) y * red ϖ k S * y - red ϖ k T ∈ hermMod σ ϖ n k := by sorry
