-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localZeta_const_mul
-- name    : GroundTheory.LocalField.localZeta_const_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:17:49.995673+00:00
-- url     : https://prove2.me/theorems/2168b2ce-06a2-554c-9196-e1041604779c
-- title:
--   Local Field: local Zeta const mul
-- statement:
--   The Local Field construction uses the local Zeta const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L134-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L134-L140

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
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
variable [MeasurableSpace K] [BorelSpace K]
variable {χ : Kˣ →* ℂˣ}

theorem GroundTheory.LocalField.localZeta_const_mul (c : ℂ) (f : K → ℂ) (s : ℂ) :
    localZeta (fun x => c * f x) χ s = c * localZeta f χ s := by sorry
