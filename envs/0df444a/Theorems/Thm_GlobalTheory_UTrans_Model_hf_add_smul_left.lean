-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Model_hf_add_smul_left
-- name    : GlobalTheory.UTrans.Model.hf_add_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:20.702804+00:00
-- url     : https://prove2.me/theorems/25b26d8e-2e26-4092-b78f-5cfecceb4ab1
-- title:
--   Model: hf add smul left
-- statement:
--   The Model construction uses the hf add smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L18-L22

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

theorem GlobalTheory.UTrans.Model.hf_add_smul_left (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (v x y : Fin n → R) (c : R) :
    hf σ G (v + c • x) y = hf σ G v y + c * hf σ G x y := by sorry
