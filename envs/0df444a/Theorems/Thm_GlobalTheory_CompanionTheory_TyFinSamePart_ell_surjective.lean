-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_ell_surjective
-- name    : GlobalTheory.CompanionTheory.TyFinSamePart.ell_surjective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:25.207811+00:00
-- url     : https://prove2.me/theorems/c1c3aee0-e5e3-45d9-95b5-febcfb3546f8
-- title:
--   Ty Fin Same Part: ell surjective
-- statement:
--   The Ty Fin Same Part construction uses the ell surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L151-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L151-L160

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

theorem GlobalTheory.CompanionTheory.TyFinSamePart.ell_surjective {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') :
    Function.Surjective (ell (K := K) b π) := by sorry
