-- Prove2me | Theorems.Thm_GroundTheory_LocalField_setIntegral_ordShell_mul
-- name    : GroundTheory.LocalField.setIntegral_ordShell_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:07.007358+00:00
-- url     : https://prove2.me/theorems/79cc9b6a-83a7-5e79-828b-23ec6fdcdfc2
-- title:
--   Local Field: set Integral ord Shell mul
-- statement:
--   The Local Field construction uses the set Integral ord Shell mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L158-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L158-L168

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
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

theorem GroundTheory.LocalField.setIntegral_ordShell_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Kˣ → E) (v : Kˣ) (k : ℤ) :
    ∫ u in ordShell K (ord (v : K) + k), F u ∂multHaar K =
      ∫ u in ordShell K k, F (v * u) ∂multHaar K := by sorry
