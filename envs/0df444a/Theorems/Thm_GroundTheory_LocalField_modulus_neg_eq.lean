-- Prove2me | Theorems.Thm_GroundTheory_LocalField_modulus_neg_eq
-- name    : GroundTheory.LocalField.modulus_neg_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:10.986496+00:00
-- url     : https://prove2.me/theorems/28382104-f897-4ce2-b442-424b59488471
-- title:
--   Local Field: modulus neg eq
-- statement:
--   The Local Field construction uses the modulus neg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L37-L40

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.modulus_neg_eq (x : K) : modulus (-x) = modulus x := by sorry
