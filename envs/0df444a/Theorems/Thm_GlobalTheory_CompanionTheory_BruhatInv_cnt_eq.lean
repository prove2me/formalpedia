-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_cnt_eq
-- name    : GlobalTheory.CompanionTheory.BruhatInv.cnt_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:04.500326+00:00
-- url     : https://prove2.me/theorems/04079961-e6da-4093-a951-f28d6dca961c
-- title:
--   Bruhat Inv: cnt eq
-- statement:
--   The Bruhat Inv construction uses the cnt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionUnique.lean#L87-L93

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

theorem GlobalTheory.CompanionTheory.BruhatInv.cnt_eq {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ τ : Equiv.Perm ι)
    (h : ∃ β ∈ parab K b', ∃ α ∈ parab K b, pm K τ = β * pm K σ * α) (a a' : ℕ) :
    cnt b b' τ a a' = cnt b b' σ a a' := by sorry
