-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MidConj_mul_single_one_mul_apply
-- name    : GlobalTheory.CompanionTheory.MidConj.mul_single_one_mul_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:16.010745+00:00
-- url     : https://prove2.me/theorems/cffafe4a-f796-40fa-b0d9-603e6e99a86f
-- title:
--   Mid Conj: mul single one mul apply
-- statement:
--   The Mid Conj construction uses the mul single one mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/AdaptedFrameOrthogonalSubspace.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/AdaptedFrameOrthogonalSubspace.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_AdaptedFrameOrthogonalSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MidConj

theorem GlobalTheory.CompanionTheory.MidConj.mul_single_one_mul_apply {l m o s : Type*} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    (A : Matrix l m ℂ) (C : Matrix o s ℂ) (x : m) (y : o) (i : l) (k : s) :
    (A * Matrix.single x y (1 : ℂ) * C) i k = A i x * C y k := by sorry
