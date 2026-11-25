-- Prove2me | Theorems.Thm_GlobalTheory_TopExt_coe_wedgeMap_tmul
-- name    : GlobalTheory.TopExt.coe_wedgeMap_tmul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:41:20.054408+00:00
-- url     : https://prove2.me/theorems/a3e549ab-ac83-569d-ba55-e512cc090d77
-- title:
--   Top Ext: coe wedge Map tmul
-- statement:
--   The Top Ext construction uses the coe wedge Map tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L48-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module Function
open GlobalTheory
open GlobalTheory.TopExt
variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]

theorem GlobalTheory.TopExt.coe_wedgeMap_tmul (i : F →ₗ[R] H) (s : L →ₗ[R] H) {a b : ℕ} (x : ⋀[R]^a F)
    (y : ⋀[R]^b L) : (wedgeMap i s a b (x ⊗ₜ y) : ExteriorAlgebra R H) =
      ExteriorAlgebra.map i (x : ExteriorAlgebra R F) *
        ExteriorAlgebra.map s (y : ExteriorAlgebra R L) := by sorry
