-- Prove2me | Theorems.Thm_GlobalTheory_Tw_Model_theta_theta
-- name    : GlobalTheory.Tw.Model.theta_theta
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:15.591128+00:00
-- url     : https://prove2.me/theorems/59880e56-fa10-4a84-b288-fac3b73299fe
-- title:
--   Model: theta theta
-- statement:
--   The Model construction uses the theta theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L66-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L66-L82

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

theorem GlobalTheory.Tw.Model.theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by sorry
