-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLSmall_small_antitone
-- name    : GlobalTheory.CompanionTheory.GLSmall.small_antitone
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:11.362045+00:00
-- url     : https://prove2.me/theorems/dc90dffa-82b6-46e4-ad66-cd1ff1835712
-- title:
--   GLSmall: small antitone
-- statement:
--   The GLSmall construction uses the small antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsLevelInverseCongruence.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsLevelInverseCongruence.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsLevelInverseCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Matrix Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLSmall
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.GLSmall.small_antitone {ϖ : k} (h : valuation k ϖ < 1) (n : ℕ) : Antitone (small ϖ n) := by sorry
