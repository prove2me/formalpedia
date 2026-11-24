-- Prove2me | Theorems.Thm_GlobalTheory_Tw_thetaGL_mul
-- name    : GlobalTheory.Tw.thetaGL_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:14:49.798854+00:00
-- url     : https://prove2.me/theorems/0986b42e-3400-436d-9de8-08341b0e3b46
-- title:
--   Tw: theta GL mul
-- statement:
--   The Tw construction uses the theta GL mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L33-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

theorem GlobalTheory.Tw.thetaGL_mul (g h : GL (Fin n) R) : thetaGL (g * h) = thetaGL g * thetaGL h := by sorry
