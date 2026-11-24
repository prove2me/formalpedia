-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_ReflStep_herm_smul_left
-- name    : GlobalTheory.UnRep.ReflStep.herm_smul_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:23:07.6004+00:00
-- url     : https://prove2.me/theorems/8e197387-ea51-4426-bf94-2594d6b69db2
-- title:
--   Refl Step: herm smul left
-- statement:
--   The Refl Step construction uses the herm smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuasiReflectionProdMulVecEq.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuasiReflectionProdMulVecEq.lean#L24-L28

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

theorem GlobalTheory.UnRep.ReflStep.herm_smul_left (x w : Fin n → E) (e : E) :
    hermE c G (e • x) w = e * hermE c G x w := by sorry
