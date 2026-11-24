-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_finite_det_one_add_smul_eq_zero
-- name    : GlobalTheory.UnRep.finite_det_one_add_smul_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:26:00.731796+00:00
-- url     : https://prove2.me/theorems/0253c8d4-049c-4be6-83f8-b0f51e99b4d9
-- title:
--   Un Rep: finite det one add smul eq zero
-- statement:
--   The Un Rep construction uses the finite det one add smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean#L10-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean#L10-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
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
open GlobalTheory GlobalTheory.UnRep

theorem GlobalTheory.UnRep.finite_det_one_add_smul_eq_zero {E K : Type} [Field E] [Field K] (φ : E →+* K) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) : {l : E | (1 + φ l • G).det = 0}.Finite := by sorry
