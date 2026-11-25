-- Prove2me | Theorems.Thm_GroundTheory_LocalField_norm_le_one_of_aeval_eq_zero
-- name    : GroundTheory.LocalField.norm_le_one_of_aeval_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:29:52.303805+00:00
-- url     : https://prove2.me/theorems/66c12726-ab3e-56fa-9dec-f4ef3004e125
-- title:
--   Local Field: norm le one of aeval eq zero
-- statement:
--   The Local Field construction uses the norm le one of aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L20-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L20-L52

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
variable {L : Type*} [NontriviallyNormedField L]

theorem GroundTheory.LocalField.norm_le_one_of_aeval_eq_zero {C : Type*} [NormedField C] [IsUltrametricDist C]
    [NormedAlgebra L C] {g : L[X]} (hg : g.Monic) (hc : ∀ i, ‖g.coeff i‖ ≤ 1) {x : C}
    (hx : aeval x g = 0) : ‖x‖ ≤ 1 := by sorry
