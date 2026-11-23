-- Prove2me | Theorems.Thm_GlobalTheory_Tw_Model_Phi_conjTranspose
-- name    : GlobalTheory.Tw.Model.Phi_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:23.13445+00:00
-- url     : https://prove2.me/theorems/006463d8-0fca-4c6a-a60a-70c7626c9d83
-- title:
--   Model: Phi conj Transpose
-- statement:
--   The Model construction uses the Phi conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L35-L38

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

theorem GlobalTheory.Tw.Model.Phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by sorry
