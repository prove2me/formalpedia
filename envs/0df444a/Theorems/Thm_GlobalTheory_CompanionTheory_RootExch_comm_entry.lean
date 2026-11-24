-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_comm_entry
-- name    : GlobalTheory.CompanionTheory.RootExch.comm_entry
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:00.914459+00:00
-- url     : https://prove2.me/theorems/4dc6daab-7014-437a-982d-786070aea59e
-- title:
--   Root Exch: comm entry
-- statement:
--   The Root Exch construction uses the comm entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L162-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L162-L194

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

theorem GlobalTheory.CompanionTheory.RootExch.comm_entry (g : GL ι K) (r t : ι) (h : r ≠ t) (s : K) (hg : (g : Matrix ι ι K) t r = 0) (i j : ι) :
    ((tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ : GL ι K) : Matrix ι ι K) i j =
      (1 : Matrix ι ι K) i j + (if i = r ∧ j = t then s else 0) -
        s * (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j := by sorry
