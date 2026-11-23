-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Model_tv_mulVec
-- name    : GlobalTheory.UTrans.Model.tv_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:47.093034+00:00
-- url     : https://prove2.me/theorems/ed6af2dd-bad9-4119-b8f5-7f7252df6c12
-- title:
--   Model: tv mul Vec
-- statement:
--   The Model construction uses the tv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L9-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_NontrivialTransvection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Model
open GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.UTrans.Model.tv_mulVec (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (x v : Fin n → R) (t : R) :
    (tv σ G x t).mulVec v = v + (t * hf σ G v x) • x := by sorry
