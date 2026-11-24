-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_tv_apply
-- name    : GlobalTheory.CompanionTheory.RootExch.tv_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:49.692739+00:00
-- url     : https://prove2.me/theorems/c8b49f97-29e1-4fe6-80cc-b9137dda8f62
-- title:
--   Root Exch: tv apply
-- statement:
--   The Root Exch construction uses the tv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L157-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L157-L160

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

theorem GlobalTheory.CompanionTheory.RootExch.tv_apply (r t : ι) (h : r ≠ t) (s : K) (i j : ι) :
    ((tv r t h s : GL ι K) : Matrix ι ι K) i j = (1 : Matrix ι ι K) i j + if i = r ∧ j = t then s else 0 := by sorry
