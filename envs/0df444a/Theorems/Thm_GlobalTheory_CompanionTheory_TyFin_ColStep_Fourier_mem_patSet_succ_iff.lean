-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Fourier_mem_patSet_succ_iff
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.mem_patSet_succ_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:17.148354+00:00
-- url     : https://prove2.me/theorems/f52c528e-8d63-4880-95f8-33ea9ef804d7
-- title:
--   Fourier: mem pat Set succ iff
-- statement:
--   The Fourier construction uses the mem pat Set succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerColumnRecursion.lean#L66-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerColumnRecursion.lean#L66-L98

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerColumnRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.mem_patSet_succ_iff {d j : ℕ} (hj : j < d) (u : GL (Fin d) K) :
    u ∈ patSet K (colGe d (j + 1)) ↔ u ∈ patSet K (colGe d j) ∧ colEntries hj u = 0 := by sorry
