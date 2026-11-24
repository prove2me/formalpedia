-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_dense_hasCompactSupport
-- name    : GlobalTheory.CompanionTheory.DiracComb.dense_hasCompactSupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:13.036288+00:00
-- url     : https://prove2.me/theorems/cd322384-4fdb-472a-b61f-fb1354b6bab5
-- title:
--   Dirac Comb: dense has Compact Support
-- statement:
--   The Dirac Comb construction uses the dense has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L164-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DenseHasCompactSupport.lean#L164-L254

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DenseHasCompactSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DiracComb

theorem GlobalTheory.CompanionTheory.DiracComb.dense_hasCompactSupport : ∀ (n : ℕ), Dense {f : SchwartzMap (Fin n → ℝ) ℂ | HasCompactSupport (f : (Fin n → ℝ) → ℂ)} := by sorry
