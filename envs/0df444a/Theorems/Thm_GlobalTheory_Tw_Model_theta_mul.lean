-- Prove2me | Theorems.Thm_GlobalTheory_Tw_Model_theta_mul
-- name    : GlobalTheory.Tw.Model.theta_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:06:07.801808+00:00
-- url     : https://prove2.me/theorems/b657cd11-3d31-410d-bbb3-198db98ec69d
-- title:
--   Model: theta mul
-- statement:
--   The Model construction uses the theta mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L53-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
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
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

theorem GlobalTheory.Tw.Model.theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by sorry
