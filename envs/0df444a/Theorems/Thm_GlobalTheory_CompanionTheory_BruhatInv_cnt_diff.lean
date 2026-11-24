-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_cnt_diff
-- name    : GlobalTheory.CompanionTheory.BruhatInv.cnt_diff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:11.905241+00:00
-- url     : https://prove2.me/theorems/b8b363c2-2488-40b1-9cd0-84837c8891aa
-- title:
--   Bruhat Inv: cnt diff
-- statement:
--   The Bruhat Inv construction uses the cnt diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L95-L104

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

theorem GlobalTheory.CompanionTheory.BruhatInv.cnt_diff {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ : Equiv.Perm ι)
    (c : Fin s) (c' : Fin s') :
    cnt b b' σ (c + 1) c' + cnt b b' σ c (c' + 1) =
      cnt b b' σ c c' + cnt b b' σ (c + 1) (c' + 1) +
        Fintype.card {i // b i = c ∧ b' (σ i) = c'} := by sorry
