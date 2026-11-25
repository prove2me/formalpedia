-- Prove2me | Theorems.Thm_GroundTheory_LocalField_selfDual_apply
-- name    : GroundTheory.LocalField.selfDual_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:19.108423+00:00
-- url     : https://prove2.me/theorems/594d50d8-fdcc-5210-b312-c71623790279
-- title:
--   Local Field: self Dual apply
-- statement:
--   The Local Field construction uses the self Dual apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierChar.lean#L396-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierChar.lean#L396-L397

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
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
open ValuativeRel Topology Filter
open scoped WithZero Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)

theorem GroundTheory.LocalField.selfDual_apply (a x : Multiplicative K) : selfDual hψ hψ1 a x = ψ (a.toAdd * x.toAdd) := by sorry

attribute [defeq] GroundTheory.LocalField.selfDual_apply
