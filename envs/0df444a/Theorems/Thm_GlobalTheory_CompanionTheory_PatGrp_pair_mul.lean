-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_pair_mul
-- name    : GlobalTheory.CompanionTheory.PatGrp.pair_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:08.552016+00:00
-- url     : https://prove2.me/theorems/11a5fe61-e8ab-4666-9ac4-f8f0ddeb1e68
-- title:
--   Pat Grp: pair mul
-- statement:
--   The Pat Grp construction uses the pair mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L185-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L185-L195

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PatGrp
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}

theorem GlobalTheory.CompanionTheory.PatGrp.pair_mul {E : ι → ι → K} (hE : IsPatChar Φ E) {A B : Matrix ι ι K}
    (hA : Supp Φ A) (hB : Supp Φ B) : pair E (A * B) = 0 := by sorry
