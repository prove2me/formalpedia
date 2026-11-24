-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_rank_cut_le
-- name    : GlobalTheory.CompanionTheory.BruhatInv.rank_cut_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:03.385274+00:00
-- url     : https://prove2.me/theorems/c707124b-5446-4aa7-a9ae-d6de50b107f2
-- title:
--   Bruhat Inv: rank cut le
-- statement:
--   The Bruhat Inv construction uses the rank cut le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L24-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L24-L42

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

theorem GlobalTheory.CompanionTheory.BruhatInv.rank_cut_le (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (A M B : Matrix ι ι K)
    (hA : ∀ i j, p i → ¬ p j → A i j = 0) (hB : ∀ i j, q j → ¬ q i → B i j = 0) :
    (ind K p * (A * M * B) * ind K q).rank ≤ (ind K p * M * ind K q).rank := by sorry
