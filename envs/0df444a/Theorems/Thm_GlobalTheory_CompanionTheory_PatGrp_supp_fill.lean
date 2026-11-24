-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_supp_fill
-- name    : GlobalTheory.CompanionTheory.PatGrp.supp_fill
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:19.331045+00:00
-- url     : https://prove2.me/theorems/2d395a67-fd5e-4106-9522-7e4eccd7baf6
-- title:
--   Pat Grp: supp fill
-- statement:
--   The Pat Grp construction uses the supp fill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L126-L130

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

theorem GlobalTheory.CompanionTheory.PatGrp.supp_fill (f : {p : ι × ι // Φ p.1 p.2} → K) : Supp Φ (fill Φ f) := by sorry
