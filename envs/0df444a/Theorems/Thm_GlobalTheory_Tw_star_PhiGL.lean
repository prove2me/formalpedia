-- Prove2me | Theorems.Thm_GlobalTheory_Tw_star_PhiGL
-- name    : GlobalTheory.Tw.star_PhiGL
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:13:29.861507+00:00
-- url     : https://prove2.me/theorems/1682a6a8-9b25-4f90-ba81-50fc75cacbac
-- title:
--   Tw: star Phi GL
-- statement:
--   The Tw construction uses the star Phi GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L36-L37

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

theorem GlobalTheory.Tw.star_PhiGL : star (PhiGL n R) = (PhiGL n R)⁻¹ := by sorry
