-- Prove2me | Theorems.Thm_GlobalTheory_Tw_Phi_inv
-- name    : GlobalTheory.Tw.Phi_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:48.769075+00:00
-- url     : https://prove2.me/theorems/66652039-78bd-4acd-ae7d-e04c55baf79c
-- title:
--   Tw: Phi inv
-- statement:
--   The Tw construction uses the Phi inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsHermitianOfMemRealScalars.lean#L23-L23

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
omit [StarRing R]

theorem GlobalTheory.Tw.Phi_inv : (Phi n R)⁻¹ = (Phi n R)ᵀ := by sorry
