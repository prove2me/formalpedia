-- Prove2me | Theorems.Thm_GlobalTheory_SqZeroPow_dual_fst_of_eps_mul
-- name    : GlobalTheory.SqZeroPow.dual_fst_of_eps_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:25:10.236921+00:00
-- url     : https://prove2.me/theorems/df3bb26a-93a9-495c-9d24-947a083ef833
-- title:
--   Sq Zero Pow: dual fst of eps mul
-- statement:
--   The Sq Zero Pow construction uses the dual fst of eps mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRingSqZeroNilpotentAugmented.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRingSqZeroNilpotentAugmented.lean#L12-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsRingSqZeroNilpotentAugmented
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SqZeroPow

theorem GlobalTheory.SqZeroPow.dual_fst_of_eps_mul {R : Type} [CommRing R] (f : DualNumber R) (r : R) (n : ℕ)
    (h : (DualNumber.eps : DualNumber R) * (TrivSqZeroExt.inl r) ^ n * f = 0) :
    r ^ n * f.fst = 0 := by sorry
