-- Prove2me | Theorems.Thm_GroundTheory_LocalField_modulus_cpow_eq_qcpow
-- name    : GroundTheory.LocalField.modulus_cpow_eq_qcpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:22.96505+00:00
-- url     : https://prove2.me/theorems/ed1aac6f-8e5f-4fcd-b687-3a047e55deb7
-- title:
--   Local Field: modulus cpow eq qcpow
-- statement:
--   The Local Field construction uses the modulus cpow eq qcpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean#L26-L32

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

theorem GroundTheory.LocalField.modulus_cpow_eq_qcpow {x : K} (hx : x ≠ 0) (z : ℂ) :
    ((modulus x : ℝ) : ℂ) ^ z = (residueCard K : ℂ) ^ (-(ord x : ℂ) * z) := by sorry
