-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_dGL_mem
-- name    : GlobalTheory.CompanionTheory.TyFinSamePart.dGL_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:16.043169+00:00
-- url     : https://prove2.me/theorems/d0f3c67d-df88-47a0-b672-51fc94680a39
-- title:
--   Ty Fin Same Part: d GL mem
-- statement:
--   The Ty Fin Same Part construction uses the d GL mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L110-L113

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

theorem GlobalTheory.CompanionTheory.TyFinSamePart.dGL_mem {s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s')
    (hb : ∀ i j, b' j < b' i → b j ≠ b i) (L : ∀ c, GL {i // b i = c} K) : dGL b L ∈ parab K b' := by sorry
