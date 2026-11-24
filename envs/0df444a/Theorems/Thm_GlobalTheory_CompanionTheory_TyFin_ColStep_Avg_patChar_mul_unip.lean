-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_patChar_mul_unip
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.patChar_mul_unip
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:14.802391+00:00
-- url     : https://prove2.me/theorems/25c5a05f-abe7-4bcb-9857-268bb4d0496f
-- title:
--   Avg: pat Char mul unip
-- statement:
--   The Avg construction uses the pat Char mul unip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerVanishesOfRadicalSums.lean#L109-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerVanishesOfRadicalSums.lean#L109-L118

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {d j : ℕ}

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.patChar_mul_unip (ψ₀ : AddChar K ℂ) {u v : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j))
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) :
    patChar (colGeE K d (j + 1)) ψ₀ (u * v) = patChar (colGeE K d (j + 1)) ψ₀ u := by sorry
