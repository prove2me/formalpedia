-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_unip_subset_patSet
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.unip_subset_patSet
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:14.42289+00:00
-- url     : https://prove2.me/theorems/b544f6f6-7acb-4e38-99b7-33258cfec76d
-- title:
--   Avg: unip subset pat Set
-- statement:
--   The Avg construction uses the unip subset pat Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerVanishesOfRadicalSums.lean#L69-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerVanishesOfRadicalSums.lean#L69-L89

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

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.unip_subset_patSet {v : GL (Fin d) K}
    (hv : v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) :
    v ∈ patSet K (colGe d j) := by sorry
