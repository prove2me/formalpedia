-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_patSet_mono
-- name    : GlobalTheory.CompanionTheory.RootExch.patSet_mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:43.047057+00:00
-- url     : https://prove2.me/theorems/7d3d62e9-d8ba-4975-b7fc-f0cb6a3882e4
-- title:
--   Root Exch: pat Set mono
-- statement:
--   The Root Exch construction uses the pat Set mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L202-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L202-L203

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

theorem GlobalTheory.CompanionTheory.RootExch.patSet_mono {Φ Ψ : ι → ι → Prop} (h : ∀ i j, Φ i j → Ψ i j) {g : GL ι K} (hg : g ∈ patSet K Φ) :
    g ∈ patSet K Ψ := by sorry
