-- Prove2me | Theorems.Thm_GroundTheory_LocalField_coeff_sum_fin_C_mul_X_pow
-- name    : GroundTheory.LocalField.coeff_sum_fin_C_mul_X_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:34.188793+00:00
-- url     : https://prove2.me/theorems/4fab4ebf-12ee-5301-be8e-7bb73a4bd26d
-- title:
--   Local Field: coeff sum fin C mul X pow
-- statement:
--   The Local Field construction uses the coeff sum fin C mul X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L169-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L169-L177

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Polynomial IntermediateField ValuativeRel
open GroundTheory GroundTheory.LocalField
variable {R : Type*} [CommRing R]

theorem GroundTheory.LocalField.coeff_sum_fin_C_mul_X_pow {n : ℕ} (c : Fin n → R) (k : ℕ) :
    (∑ i : Fin n, C (c i) * X ^ (i : ℕ)).coeff k = if h : k < n then c ⟨k, h⟩ else 0 := by sorry
