-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_tv_mem
-- name    : GlobalTheory.CompanionTheory.RootExch.tv_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:17.431337+00:00
-- url     : https://prove2.me/theorems/e3d5d805-6d26-465e-8f0b-c4a0098f7b36
-- title:
--   Root Exch: tv mem
-- statement:
--   The Root Exch construction uses the tv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L205-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L205-L219

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.RootExch.tv_mem {Ψ : ι → ι → Prop} (r t : ι) (h : r ≠ t) (s : K) (hrt : Ψ r t) :
    tv r t h s ∈ patSet K Ψ := by sorry
