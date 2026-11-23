-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PatGrp_coe_patSubgroup
-- name    : GlobalTheory.CompanionTheory.PatGrp.coe_patSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:27.113496+00:00
-- url     : https://prove2.me/theorems/280aa25b-cd26-4d04-a668-6f177fe1d9bc
-- title:
--   Pat Grp: coe pat Subgroup
-- statement:
--   The Pat Grp construction uses the coe pat Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L118-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternGroupStatement.lean#L118-L119

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

theorem GlobalTheory.CompanionTheory.PatGrp.coe_patSubgroup (h : IsPat Φ) :
    ((patSubgroup h : Subgroup (GL ι K)) : Set (GL ι K)) = patSet K Φ := by sorry
