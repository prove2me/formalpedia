-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_ReflStep_herm_sub_smul_right
-- name    : GlobalTheory.UnRep.ReflStep.herm_sub_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:21.621419+00:00
-- url     : https://prove2.me/theorems/33d0e4a8-59f7-4887-a0ec-9e775d330b1f
-- title:
--   Refl Step: herm sub smul right
-- statement:
--   The Refl Step construction uses the herm sub smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuasiReflectionProdMulVecEq.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuasiReflectionProdMulVecEq.lean#L17-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.ReflStep
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.UnRep.ReflStep.herm_sub_smul_right (z x w : Fin n → E) (e : E) :
    hermE c G w (z - e • x) = hermE c G w z - c e * hermE c G w x := by sorry
