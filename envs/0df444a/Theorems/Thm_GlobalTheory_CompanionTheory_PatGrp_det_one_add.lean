-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_det_one_add
-- name    : GlobalTheory.CompanionTheory.PatGrp.det_one_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:42.507806+00:00
-- url     : https://prove2.me/theorems/40543ed5-ee1f-4472-b559-b8abee906554
-- title:
--   Pat Grp: det one add
-- statement:
--   The Pat Grp construction uses the det one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L54-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L54-L88

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

theorem GlobalTheory.CompanionTheory.PatGrp.det_one_add (h : IsPat Φ) {N : Matrix ι ι K} (hN : Supp Φ N) : (1 + N).det = 1 := by sorry
