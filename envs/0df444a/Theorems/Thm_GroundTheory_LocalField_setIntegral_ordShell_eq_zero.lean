-- Prove2me | Theorems.Thm_GroundTheory_LocalField_setIntegral_ordShell_eq_zero
-- name    : GroundTheory.LocalField.setIntegral_ordShell_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:51.49004+00:00
-- url     : https://prove2.me/theorems/60aa970f-2aed-4b0f-88f2-9bee3c1359dd
-- title:
--   Local Field: set Integral ord Shell eq zero
-- statement:
--   The Local Field construction uses the set Integral ord Shell eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L181-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L181-L191

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

theorem GroundTheory.LocalField.setIntegral_ordShell_eq_zero (F : Kˣ → ℂ) {v : Kˣ} (hv : ord (v : K) = 0) {a : ℂ}
    (ha : a ≠ 1) (k : ℤ) (hF : ∀ u ∈ ordShell K k, F (v * u) = a * F u) :
    ∫ u in ordShell K k, F u ∂multHaar K = 0 := by sorry
