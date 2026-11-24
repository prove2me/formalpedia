-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_rank_cut_pm
-- name    : GlobalTheory.CompanionTheory.BruhatInv.rank_cut_pm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:26:43.155565+00:00
-- url     : https://prove2.me/theorems/914c0088-85fc-4fd7-ad09-808e20b9bc9b
-- title:
--   Bruhat Inv: rank cut pm
-- statement:
--   The Bruhat Inv construction uses the rank cut pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L50-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L50-L66

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

theorem GlobalTheory.CompanionTheory.BruhatInv.rank_cut_pm (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (σ : Equiv.Perm ι) :
    (ind K p * ((pm K σ : GL ι K) : Matrix ι ι K) * ind K q).rank =
      (Finset.univ.filter fun j => q j ∧ p (σ j)).card := by sorry
