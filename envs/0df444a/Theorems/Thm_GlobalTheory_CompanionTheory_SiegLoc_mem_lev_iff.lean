-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_mem_lev_iff
-- name    : GlobalTheory.CompanionTheory.SiegLoc.mem_lev_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:16.541903+00:00
-- url     : https://prove2.me/theorems/c00619de-4f20-43b1-a97f-5f5ea2c24aa7
-- title:
--   Sieg Loc: mem lev iff
-- statement:
--   The Sieg Loc construction uses the mem lev iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FixedNondeg.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FixedNondeg.lean#L20-L21

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.SiegLoc.mem_lev_iff {ϖ : R} {k : ℕ} {a : R} : a ∈ lev ϖ k ↔ ∃ c, a = ϖ ^ k * c := by sorry
