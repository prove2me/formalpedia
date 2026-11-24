-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_nz_of_mem
-- name    : GlobalTheory.CompanionTheory.RootExch.nz_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:20.096151+00:00
-- url     : https://prove2.me/theorems/d0066487-6b29-40fb-a3c3-b1826f72974a
-- title:
--   Root Exch: nz of mem
-- statement:
--   The Root Exch construction uses the nz of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L196-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L196-L200

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

theorem GlobalTheory.CompanionTheory.RootExch.nz_of_mem {Φ : ι → ι → Prop} {g : GL ι K} (hg : g ∈ patSet K Φ) {i j : ι}
    (h : (g : Matrix ι ι K) i j ≠ 0) : i = j ∨ Φ i j := by sorry
