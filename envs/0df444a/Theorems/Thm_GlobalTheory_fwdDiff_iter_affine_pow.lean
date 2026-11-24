-- Prove2me | Theorems.Thm_GlobalTheory_fwdDiff_iter_affine_pow
-- name    : GlobalTheory.fwdDiff_iter_affine_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:35.078139+00:00
-- url     : https://prove2.me/theorems/6bfae756-3cde-41be-800e-0f21852c39e8
-- title:
--   Global Theory: fwd Diff iter affine pow
-- statement:
--   The Global Theory construction uses the fwd Diff iter affine pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/AlternatingSumChooseMulSubPow.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/AlternatingSumChooseMulSubPow.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_AlternatingSumChooseMulSubPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset

theorem GlobalTheory.fwdDiff_iter_affine_pow (g : ℕ) (a b y : ℤ) :
    (fwdDiff (1 : ℤ))^[g] (fun r : ℤ => (a * r + b) ^ g) y = g.factorial * a ^ g := by sorry
