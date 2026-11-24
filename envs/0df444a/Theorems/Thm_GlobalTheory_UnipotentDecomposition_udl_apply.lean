-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentDecomposition_udl_apply
-- name    : GlobalTheory.UnipotentDecomposition.udl_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:25:17.920816+00:00
-- url     : https://prove2.me/theorems/b5dc94ad-2cdd-4fdb-afe2-3a53d2307ee0
-- title:
--   Unipotent Decomposition: udl apply
-- statement:
--   The Unipotent Decomposition construction uses the udl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UdlApply.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UdlApply.lean#L7-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentDecomposition
open Matrix

theorem GlobalTheory.UnipotentDecomposition.udl_apply {O : Type} [CommRing O] {m : ℕ} (A B : Matrix (Fin m) (Fin m) O) (d : Fin m → O) (i j : Fin m) :
    (A * Matrix.diagonal d * B) i j = ∑ k, A i k * d k * B k j := by sorry
