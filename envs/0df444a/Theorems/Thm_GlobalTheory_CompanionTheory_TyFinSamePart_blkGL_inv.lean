-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_blkGL_inv
-- name    : GlobalTheory.CompanionTheory.TyFinSamePart.blkGL_inv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:18.863378+00:00
-- url     : https://prove2.me/theorems/97add7cd-1ce2-4df0-b954-70f6a301aa1e
-- title:
--   Ty Fin Same Part: blk GL inv
-- statement:
--   The Ty Fin Same Part construction uses the blk GL inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L129-L132

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

theorem GlobalTheory.CompanionTheory.TyFinSamePart.blkGL_inv (b : ι → Fin s) (c : Fin s) {g : GL ι K} (h : g ∈ parab K b) :
    blkGL b c g⁻¹ = (leviHom b ⟨g, h⟩ c)⁻¹ := by sorry
