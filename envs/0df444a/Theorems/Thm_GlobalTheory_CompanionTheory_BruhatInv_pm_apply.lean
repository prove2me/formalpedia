-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_pm_apply
-- name    : GlobalTheory.CompanionTheory.BruhatInv.pm_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:04.562857+00:00
-- url     : https://prove2.me/theorems/4d185e29-a2a8-4466-9c1f-38fcb918a9c8
-- title:
--   Bruhat Inv: pm apply
-- statement:
--   The Bruhat Inv construction uses the pm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L44-L48

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BruhatInv
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.BruhatInv.pm_apply (σ : Equiv.Perm ι) (i j : ι) :
    ((pm K σ : GL ι K) : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by sorry
