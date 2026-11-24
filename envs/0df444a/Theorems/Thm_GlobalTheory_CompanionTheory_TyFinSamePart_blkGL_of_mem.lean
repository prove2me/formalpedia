-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_blkGL_of_mem
-- name    : GlobalTheory.CompanionTheory.TyFinSamePart.blkGL_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:16.088106+00:00
-- url     : https://prove2.me/theorems/4fbe5ab5-0d6d-4cd9-b2e7-c3fffc92176f
-- title:
--   Ty Fin Same Part: blk GL of mem
-- statement:
--   The Ty Fin Same Part construction uses the blk GL of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L126-L127

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSamePart
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

theorem GlobalTheory.CompanionTheory.TyFinSamePart.blkGL_of_mem (b : ι → Fin s) (c : Fin s) {g : GL ι K} (h : g ∈ parab K b) :
    blkGL b c g = leviHom b ⟨g, h⟩ c := by sorry
