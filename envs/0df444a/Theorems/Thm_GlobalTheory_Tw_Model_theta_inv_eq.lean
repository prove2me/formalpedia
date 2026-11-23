-- Prove2me | Theorems.Thm_GlobalTheory_Tw_Model_theta_inv_eq
-- name    : GlobalTheory.Tw.Model.theta_inv_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:47.918478+00:00
-- url     : https://prove2.me/theorems/f8f5562b-17e9-4915-9265-8c15c8f8c361
-- title:
--   Model: theta inv eq
-- statement:
--   The Model construction uses the theta inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L61-L64

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

theorem GlobalTheory.Tw.Model.theta_inv_eq {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    (theta g)⁻¹ = Phi n R * gᴴ * (Phi n R)ᵀ := by sorry
