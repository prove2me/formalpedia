-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_blkGL_ren
-- name    : GlobalTheory.CompanionTheory.TyFinSamePart.blkGL_ren
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:22.60984+00:00
-- url     : https://prove2.me/theorems/dc365527-2550-474b-a77e-c0bc7c49092f
-- title:
--   Ty Fin Same Part: blk GL ren
-- statement:
--   The Ty Fin Same Part construction uses the blk GL ren property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L139-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L139-L145

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

theorem GlobalTheory.CompanionTheory.TyFinSamePart.blkGL_ren {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') (c : Fin s) {g : GL ι K}
    (h : g ∈ parab K b) (h' : g ∈ parab K (π ∘ b)) :
    blkGL (π ∘ b) (π c) g = glEquiv K (ren b π c) (leviHom b ⟨g, h⟩ c) := by sorry
